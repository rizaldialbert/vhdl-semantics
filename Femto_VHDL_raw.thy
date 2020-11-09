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
          Bits_Int_Aux
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

(* instantiation set :: (type) zero
begin

definition zero_set :: "'a set" where
  "zero_set = {}"

instance proof qed
end
 *)

lemma upd_eventually_cofinite:
  assumes  "\<forall>\<^sub>\<infinity>n. f n = 0"
  shows "\<forall>\<^sub>\<infinity>n. (f(m := k)) n = 0"
  using assms
  by (smt MOST_neq(2) eventually_elim2 fun_upd_def)

term "override_on"

lemma 
  assumes  "\<forall>\<^sub>\<infinity>n. f n = 0"
  assumes  "\<forall>\<^sub>\<infinity>n. g n = 0"
  shows    "\<forall>\<^sub>\<infinity>n. override_on f g A n = 0"
proof -
  have "\<forall>p pa f pb. (eventually pb f \<and> eventually pa f \<and> (\<forall>a. pb (a::'a) \<and> pa a \<longrightarrow> p a) \<longrightarrow> eventually p f) = ((\<not> eventually pb f \<or> \<not> eventually pa f \<or> (\<exists>a. (pb a \<and> pa a) \<and> \<not> p a)) \<or> eventually p f)"
    by blast
  then have f1: "\<forall>p f pa pb. (\<not> eventually p f \<or> \<not> eventually pa f \<or> (\<exists>a. (p (a::'a) \<and> pa a) \<and> \<not> pb a)) \<or> eventually pb f"
    by (smt eventually_elim2)
  obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
    "\<forall>x0 x1 x3. (\<exists>v4. (x3 v4 \<and> x1 v4) \<and> \<not> x0 v4) = ((x3 (aa x0 x1 x3) \<and> x1 (aa x0 x1 x3)) \<and> \<not> x0 (aa x0 x1 x3))"
    by moura
  then have f2: "\<forall>p f pa pb. \<not> eventually p f \<or> \<not> eventually pa f \<or> p (aa pb pa p) \<and> pa (aa pb pa p) \<and> \<not> pb (aa pb pa p) \<or> eventually pb f"
    using f1 by presburger
  have "f (aa (\<lambda>a. override_on f g A a = 0) (\<lambda>a. g a = 0) (\<lambda>a. f a = 0)) \<noteq> 0 \<or> g (aa (\<lambda>a. override_on f g A a = 0) (\<lambda>a. g a = 0) (\<lambda>a. f a = 0)) \<noteq> 0 \<or> override_on f g A (aa (\<lambda>a. override_on f g A a = 0) (\<lambda>a. g a = 0) (\<lambda>a. f a = 0)) = 0"
    by (simp add: override_on_def)
  then show ?thesis
    using f2  by (smt assms(1) assms(2))
qed


lemma upd_eventually_cofinite_override_on_finite:
  assumes  "finite A"
  assumes  "\<forall>\<^sub>\<infinity>n. f n = 0"
  shows    "\<forall>\<^sub>\<infinity>n. override_on f g A n = 0"
  using assms
proof (induction A)
  case empty
  then show ?case 
    unfolding override_on_def by auto
next
  case (insert x F)
  hence "\<forall>\<^sub>\<infinity>n. override_on f g F n = 0"
    by auto
  then show ?case 
    unfolding override_on_insert'
    by (metis override_on_insert override_on_insert' upd_eventually_cofinite)
qed

subsection "Core syntax"

text \<open>There are three elements of VHDL's syntax: expression, sequential statements, and concurrent
statements. Each data type for these elements is parameterised with a type variable. This type
variable is the placeholder for the type of the signals in a VHDL text. \<close>

type_synonym delay = nat

text \<open> Expressions contain logical operations such as conjunction, disjunction, etc. Included in
this expression are the construct for detecting whether a signal has changed from its previous value
--- @{term "Bsig_event"}. Construct @{term "Bsig_delayed"} checks the signal value in the previous
@{term "delay"} unit of time.\<close>

datatype signedness = Neu  (* neutral, uninterpreted *)
                    | Sig  (* signed *)
                    | Uns  (* unsigned *)

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
  | Bslice 'signal nat nat
  | Bindex 'signal nat
  | Badd  "'signal bexp" "'signal bexp"
  | Bmult "'signal bexp" "'signal bexp"
  | Bsub  "'signal bexp" "'signal bexp"
  | Bshiftl  "'signal bexp" nat              (* corresponds to shift_left in numeric_std  *)
  | Bshiftr  "'signal bexp" nat              (* corresponds to shift_right in numeric_std *)
  | Bwhen "'signal bexp" "'signal bexp" "'signal bexp"
  | Bliteral signedness "bool list"

text \<open>Sequential statements in VHDL are standard. They include skip statements @{term "Bnull"},
sequential compositions @{term "Bcomp"}, branching statements @{term "Bguarded"}, and assignments.
Two types of assignment are formalised here: transport and inertial. The explanation of these two
assignments are best explained elsewhere (for example here \<^url>\<open>http://gmvhdl.com/delay.htm\<close>).
\<close>

datatype 'signal choices = Explicit (pattern: "'signal bexp") | Others

datatype 'signal seq_stmt =
    Bcomp "'signal seq_stmt" "'signal seq_stmt"
  | Bguarded "'signal bexp" "'signal seq_stmt" "'signal seq_stmt"
  | Bassign_trans 'signal "'signal bexp" delay
  | Bassign_inert 'signal "'signal bexp" delay
  | Bnull
  | Bcase "'signal bexp" "('signal choices \<times> 'signal seq_stmt) list"

fun nonneg_delay :: "'signal seq_stmt \<Rightarrow> bool" where
  "nonneg_delay Bnull = True"
| "nonneg_delay (Bcomp s1 s2) \<longleftrightarrow> nonneg_delay s1 \<and> nonneg_delay s2"
| "nonneg_delay (Bguarded g s1 s2) \<longleftrightarrow> nonneg_delay s1 \<and> nonneg_delay s2"
| "nonneg_delay (Bassign_trans sig exp dly) \<longleftrightarrow> 0 < dly"
| "nonneg_delay (Bassign_inert sig exp dly) \<longleftrightarrow> 0 < dly"
| "nonneg_delay (Bcase exp choices) \<longleftrightarrow> list_all nonneg_delay (map snd choices)"

fun signals_in :: "'signal seq_stmt \<Rightarrow> 'signal list" where
  "signals_in (Bnull) = []"
| "signals_in (Bassign_trans sig _ _) = [sig]"
| "signals_in (Bassign_inert sig _ _) = [sig]"
| "signals_in (Bguarded sig ss1 ss2) =  remdups (signals_in ss1 @ signals_in ss2)"
| "signals_in (Bcomp ss1 ss2) = remdups (signals_in ss1 @ signals_in ss2)"
| "signals_in (Bcase exp choices) = remdups (concat (map (signals_in o snd) choices))"

lemma
  "distinct (signals_in ss)"
  by (induction ss) (auto)

abbreviation
  "signals_of s \<equiv> set (signals_in s)"

lemma [simp]:
  "signals_of (Bcase exp (choice # choices)) = signals_of (snd choice) \<union> signals_of (Bcase exp choices)"
  by auto

text \<open>Concurrent statements in VHDL is very simple: it is either a process running by itself, or
a composition of several processes. Each process is a sequential statement guarded by its
sensitivity list --- a set of signals which, if any of them changes, will trigger the execution of
the process it guards.\<close>

datatype 'signal conc_stmt =
      Bpar "'signal conc_stmt" "'signal conc_stmt" ( infixr "||" 80)
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

datatype val = Bv (bval_of : bool) | Lv (sign_of: signedness) (lval_of : "bool list")

type_synonym 'signal event = "'signal set"
type_synonym 'signal state = "'signal \<Rightarrow> val"

type_synonym 'signal valuation = "'signal \<rightharpoonup> val"

\<comment> \<open> represents scheduling \<close>
type_synonym 'signal trans_raw         = "nat \<Rightarrow> 'signal \<rightharpoonup> val"
type_synonym 'signal trans_raw_sig     = "'signal \<Rightarrow> nat \<rightharpoonup> val"
(* type_synonym 'signal trans_raw_sig_bit = "'signal \<Rightarrow> nat \<Rightarrow> (nat \<rightharpoonup> bool)" *)

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

lemma inf_time_equal_when_same_trans_upto2:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> \<tau>1 n sig =  \<tau>2 n sig"
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

lemma inf_time_update:
  assumes "\<And>n. t \<le> n \<Longrightarrow> \<theta> n = 0"
  assumes "res = \<theta>(t := Some o \<sigma>)"
  assumes "t \<le> i"
  shows "inf_time (to_trans_raw_sig res) sig i = Some t"
proof (rule inf_time_someI)
  show "t \<in> dom (to_trans_raw_sig res sig)"
    using assms(2)  by (simp add: domIff to_trans_raw_sig_def)
next
  { fix ta
    assume "ta \<in> dom (to_trans_raw_sig res sig)"
    assume "ta \<le> i"
    assume "\<not> ta \<le> t"
    hence "t < ta"
      by auto
    hence "res ta = \<theta> ta"
      unfolding assms(2) by auto
    also have "... = 0"
      using assms(1) \<open>\<not> ta \<le> t\<close> nat_le_linear by blast
    finally have "res ta = 0"
      by auto
    hence "ta \<notin> dom (to_trans_raw_sig res sig)"
      using dom_imp_keys keys_def by fastforce
    with `ta \<in> dom (to_trans_raw_sig res sig)` have False by auto }
  thus "\<forall>ta\<in>dom (to_trans_raw_sig res sig). ta \<le> i \<longrightarrow> ta \<le> t "
    by auto
qed (auto simp add: assms(3))


definition to_signal :: "val \<Rightarrow> 'signal trans_raw_sig \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> val" where
  "to_signal def \<tau> sig t = (case inf_time \<tau> sig t of
                              None    \<Rightarrow> def
                            | Some t' \<Rightarrow> the ((\<tau> sig) t'))"

lemma inf_time_ex1:
  assumes "\<exists>k\<in> keys(\<tau> sig). k \<le> n"
  shows "the (inf_time \<tau> sig n) = (GREATEST k. k \<in> keys (\<tau> sig) \<and> k \<le> n)"
  using assms unfolding inf_time_def by auto

lemma inf_time_ex2:
  assumes "\<not> (\<exists>k\<in> keys(\<tau> sig). k \<le> n)"
  shows "inf_time \<tau> sig n = None"
  using assms unfolding inf_time_def by auto

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

lemma to_signal_equal_when_trans_equal_upto2:
  fixes \<tau>1 \<tau>2 :: "'signal trans_raw"
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> \<tau>1 n sig = \<tau>2 n sig"
  assumes "n \<le> maxtime"
  shows "to_signal def (to_trans_raw_sig \<tau>1) sig n = to_signal def (to_trans_raw_sig \<tau>2) sig n"
proof -
  have "inf_time (to_trans_raw_sig \<tau>1) sig n = inf_time (to_trans_raw_sig \<tau>2) sig n"
    using inf_time_equal_when_same_trans_upto2 assms by metis
  moreover have "\<And>n. n \<le> maxtime \<Longrightarrow> (to_trans_raw_sig \<tau>1 sig) n =  (to_trans_raw_sig \<tau>2 sig) n"
    using assms unfolding to_trans_raw_sig_def by auto
  ultimately show ?thesis
    using assms unfolding to_signal_def by (auto dest!: inf_time_at_most split:option.splits)
qed

abbreviation "signal_of def \<equiv> to_signal def o to_trans_raw_sig"

lemma signal_of_def:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n s = 0"
  shows "signal_of def \<tau> s t = def"
proof -
  have "inf_time (to_trans_raw_sig \<tau>) s t = None"
    unfolding sym[OF inf_time_none_iff] using assms
    by (metis domIff leI to_trans_raw_sig_def zero_option_def)
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

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
  shows "  \<exists>m \<le> k.  to_trans_raw_sig \<tau> sig m = Some val \<and> (\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None)
        \<or> (\<forall>i. i \<le> k \<longrightarrow> \<tau> i sig = None) \<and> val = def"
proof (cases "inf_time (to_trans_raw_sig \<tau>) sig k = None")
  case True
  hence "\<forall>ka\<le>k. \<tau> ka sig = None"
    using inf_time_noneE2[OF True]  by (simp add: to_trans_raw_sig_def zero_option_def)
  moreover have "val = def"
    using assms True unfolding to_signal_def comp_def by auto
  ultimately show "(\<exists>m \<le> k.  to_trans_raw_sig \<tau> sig m = Some val \<and> (\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None)
        \<or> (\<forall>i. i \<le> k \<longrightarrow> \<tau> i sig = None) \<and> val = def)"
    by auto
next
  case False
  then obtain t' where *: "inf_time (to_trans_raw_sig \<tau>) sig k = Some t'"
    by (meson inf_time_def)
  have snd: "\<forall>j > t'. j \<le> k \<longrightarrow> (to_trans_raw_sig \<tau>) sig j = None"
    by (metis "*" domIff inf_time_someE not_le)
  have "t' \<in> keys ((to_trans_raw_sig \<tau>) sig) \<and> t' \<le> k"
    using inf_time_some_exists[OF *] by auto
  then obtain val' where "(to_trans_raw_sig \<tau>) sig t' = Some val'" and "t' \<le> k"
    unfolding to_trans_raw_sig_def keys_def by (auto simp add: zero_option_def)
  moreover have "the ((to_trans_raw_sig \<tau>) sig t') = val"
    using assms * unfolding to_signal_def comp_def by auto
  ultimately have "val = val'"
    by auto
  with \<open>t' \<le> k\<close> have "((to_trans_raw_sig \<tau>) sig) t' = Some val"
    using \<open> (to_trans_raw_sig \<tau>) sig t' = Some val'\<close> by auto
  with snd show ?thesis
    using \<open>t' \<le> k\<close> by (auto intro!: exI[where x="t'"])
qed

lemma signal_of_intro:
  assumes "(\<exists>m \<le> k.  to_trans_raw_sig \<tau> sig m = Some val \<and> (\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None) \<or> (\<forall>i. i \<le> k \<longrightarrow> \<tau> i sig = None) \<and> val = def)"
  shows "signal_of def \<tau> sig k = val"
proof -
  { assume "\<exists>m \<le> k.  to_trans_raw_sig \<tau> sig m = Some val \<and> (\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None)"
    then obtain m where "m \<le> k" and "to_trans_raw_sig \<tau> sig m = Some val" and  "\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None"
      by blast
    have "inf_time (to_trans_raw_sig \<tau>) sig k = Some m"
    proof (rule inf_time_someI)
      show "m \<in> dom (to_trans_raw_sig \<tau> sig)"
        by (simp add: \<open>to_trans_raw_sig \<tau> sig m = Some val\<close> domIff)
    next
      show "m \<le> k"
        by (simp add: \<open>m \<le> k\<close>)
    next
      show "\<forall>t\<in>dom (to_trans_raw_sig \<tau> sig). t \<le> k \<longrightarrow> t \<le> m"
        by (meson \<open>\<forall>j>m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None\<close> domIff not_le_imp_less)
    qed
    hence "signal_of def \<tau> sig k = val"
      unfolding to_signal_def comp_def
      by (simp add: \<open>to_trans_raw_sig \<tau> sig m = Some val\<close>) }
  moreover
  { assume "(\<forall>i. i \<le> k \<longrightarrow> \<tau> i sig = None) \<and> val = def"
    hence "signal_of def \<tau> sig k = val"
      by (metis option.distinct(1) signal_of_elim to_trans_raw_sig_def) }
  ultimately show "signal_of def \<tau> sig k = val"
    using assms by auto
qed

lemma signal_of_val_eq:
  "signal_of def \<tau> sig k = val \<longleftrightarrow>
  (\<exists>m \<le> k.  to_trans_raw_sig \<tau> sig m = Some val \<and> (\<forall>j > m. j \<le> k \<longrightarrow> to_trans_raw_sig \<tau> sig j = None) \<or> (\<forall>i. i \<le> k \<longrightarrow> \<tau> i sig = None) \<and> val = def)"
  apply rule
   apply (erule signal_of_elim)
  apply (erule signal_of_intro)
  done

(* definition to_trans_raw_bit :: "'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> 'signal trans_raw" where
  "to_trans_raw_bit \<tau> idx sig' = (\<lambda>n sig. if sig \<noteq> sig' then \<tau> n sig else 
                                              case \<tau> n sig of None   \<Rightarrow> None
                                                            | Some v \<Rightarrow> (case v of Bv b    \<Rightarrow> (Some o Bv)  b 
                                                                                 | Lv _ bs \<Rightarrow> (Some o Bv) (bs ! idx)))"

lemma to_trans_raw_bit_alt_def:
  "to_trans_raw_bit \<tau> idx sig' = override_on \<tau> 
          (\<lambda>n sig. if sig \<noteq> sig' then \<tau> n sig else case the (\<tau> n sig) of Bv b \<Rightarrow> Some (Bv b) | Lv _ bs \<Rightarrow> (Some o Bv) (bs ! idx)) 
          (keys (to_trans_raw_sig \<tau> sig'))"
  unfolding to_trans_raw_bit_def override_on_def comp_def
  apply (rule ext)+
  by (auto split:val.splits option.splits simp add: to_trans_raw_sig_def keys_def zero_option_def)
 *)

fun to_bit :: "nat \<Rightarrow> val \<Rightarrow> val" where
  "to_bit _ (Bv b) = Bv b"
| "to_bit b (Lv _ bs) = Bv (bs ! b)"

definition to_trans_raw_bit :: "val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> 'signal trans_raw" where
  "to_trans_raw_bit def \<tau> idx sig' = (\<lambda>n sig. if sig \<noteq> sig' then \<tau> n sig else 
                                              case \<tau> n sig of None   \<Rightarrow> None
                                                            | Some v \<Rightarrow> if 0 < n \<and> to_bit idx (signal_of def \<tau> sig (n - 1)) = to_bit idx v  then None 
                                                                        else if n = 0 \<and> to_bit idx def = to_bit idx v then None 
                                                                        else Some (to_bit idx v))"

lemma to_trans_raw_bit_alt_def:
  "to_trans_raw_bit def \<tau> idx sig' = override_on \<tau> 
          (\<lambda>n sig. if sig \<noteq> sig' then \<tau> n sig else case (\<tau> n sig) of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < n \<and> to_bit idx (signal_of def \<tau> sig (n - 1)) = to_bit idx v  then None 
                                                                        else if n = 0 \<and> to_bit idx def = to_bit idx v then None 
                                                                        else Some (to_bit idx v)) 
          (keys (to_trans_raw_sig \<tau> sig'))"
  unfolding to_trans_raw_bit_def override_on_def comp_def
  apply (rule ext)+
  by (auto split:val.splits option.splits simp add: to_trans_raw_sig_def keys_def zero_option_def)
  
type_synonym 'signal history = "'signal trans_raw"

subsection \<open>Semantics of @{typ "'signal bexp"}\<close>

fun xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<longleftrightarrow> (x \<or> y) \<and> (x \<noteq> y)"

text \<open>The semantics of expression is standard. A slightly more involved denotation is for @{term
"Bsig_delayed"}. Basically, it gets the value in the history @{term "snd \<theta> :: 'signal trans_raw"} at
time @{term "now - t"} where @{term "t"} is the delay.\<close>

inductive beval_raw :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal history \<Rightarrow> 'signal state \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
  ("_ , _ , _ , _, _  \<turnstile> _ \<longrightarrow>\<^sub>b _")
  where
  "beval_raw now \<sigma> \<gamma> \<theta> def (Bsig sig) (\<sigma> sig)"
| "beval_raw now \<sigma> \<gamma> \<theta> def (Btrue) (Bv True)"
| "beval_raw now \<sigma> \<gamma> \<theta> def (Bfalse) (Bv False)"
| "beval_raw now \<sigma> \<gamma> \<theta> def (Bsig_delayed sig t) (signal_of (def sig) \<theta> sig (now - t))"
| "beval_raw now \<sigma> \<gamma> \<theta> def (Bsig_event sig) (Bv (sig \<in> \<gamma>))"
| "beval_raw now \<sigma> \<gamma> \<theta> def e (Bv bool) \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def (Bnot e) (Bv (\<not> bool))"
| "beval_raw now \<sigma> \<gamma> \<theta> def e (Lv ki bs) \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def (Bnot e) (Lv ki (map Not bs))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1 (Bv val1); beval_raw now \<sigma> \<gamma> \<theta>  def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                           beval_raw now \<sigma> \<gamma> \<theta>  def (Band e1 e2) (Bv ( val1 \<and> val2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1 (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta>  def e2 (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                  \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta>  def (Band e1 e2) (Lv ki (map2 (\<and>) bs1 bs2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1 (Bv val1); beval_raw now \<sigma> \<gamma> \<theta>  def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                            beval_raw now \<sigma> \<gamma> \<theta> def (Bor e1 e2) (Bv ( val1 \<or> val2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1 (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta>  def e2 (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                   \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta>  def (Bor e1 e2) (Lv ki (map2 (\<or>) bs1 bs2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1 (Bv val1); beval_raw now \<sigma> \<gamma> \<theta>  def e2 (Bv val2)\<rbrakk> \<Longrightarrow>
                                        beval_raw now \<sigma> \<gamma> \<theta>  def (Bnand e1 e2) (Bv (\<not>(val1 \<and> val2)))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta>  def e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                    \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta>  def (Bnand e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> (x \<and> y)) bs1 bs2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Bv val1); beval_raw now \<sigma> \<gamma> \<theta> def  e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                         beval_raw now \<sigma> \<gamma> \<theta> def  (Bnor e1 e2)  (Bv (\<not>(val1 \<or> val2)))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta> def  e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                     \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta>  def (Bnor e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> (x \<or> y)) bs1 bs2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Bv val1); beval_raw now \<sigma> \<gamma> \<theta> def e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                          beval_raw now \<sigma> \<gamma> \<theta> def (Bxor e1 e2)  (Bv (xor val1 val2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta>  def e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                                   \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def (Bxor e1 e2)  (Lv ki (map2 xor bs1 bs2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Bv val1); beval_raw now \<sigma> \<gamma> \<theta> def e2  (Bv val2)\<rbrakk> \<Longrightarrow>
                                       beval_raw now \<sigma> \<gamma> \<theta> def (Bxnor e1 e2)  (Bv (\<not> xor val1 val2))"
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta>  def e1  (Lv ki bs1); beval_raw now \<sigma> \<gamma> \<theta> def  e2  (Lv ki bs2); length bs1 = length bs2\<rbrakk>
                    \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def  (Bxnor e1 e2)  (Lv ki (map2 (\<lambda>x y. \<not> xor x y) bs1 bs2))"

\<comment> \<open>we assume big endian here; that is why we have the expression @{term "{r..l}"} instead of
@{term "{l .. r}"}; the left index should be bigger than the right index, e.g. DATA[31 DOWNTO 0] or,
in our concrete syntax, Bslice DATA 31 0.\<close>

| "beval_raw now \<sigma> \<gamma> \<theta> def (Bsig sig) (Lv ki bs) \<Longrightarrow> length bs = len \<Longrightarrow>
                beval_raw now \<sigma> \<gamma> \<theta> def (Bslice sig l r) (Lv ki (nths bs {len - l - 1 .. len - r - 1}))"

| "beval_raw now \<sigma> \<gamma> \<theta> def (Bsig sig) (Lv ki bs) \<Longrightarrow>
                                            beval_raw now \<sigma> \<gamma> \<theta> def (Bindex sig idx) (Bv (bs ! idx))"

\<comment> \<open>unsigned addition\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2);
    len = max (length bs1) (length bs2); bs = bin_to_bl len (bl_to_bin bs1 + bl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Uns bs)"

\<comment> \<open>signed addition\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2);
    len = max (length bs1) (length bs2);  bs = bin_to_bl len (sbl_to_bin bs1 + sbl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Sig bs)"

\<comment> \<open>unsigned multiplication\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2);
    len = (length bs1) + (length bs2); bs = bin_to_bl len (bl_to_bin bs1 * bl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bmult e1 e2) (Lv Uns bs)"

\<comment> \<open>signed multiplication\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2);
    len = (length bs1) + (length bs2); bs = bin_to_bl len (sbl_to_bin bs1 * sbl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bmult e1 e2) (Lv Sig bs)"

\<comment> \<open>unsigned subtraction\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2);
    len = max (length bs1) (length bs2); bs = bin_to_bl len (bl_to_bin bs1 - bl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Uns bs)"

\<comment> \<open>signed subtraction\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1);   beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2);
    len = max (length bs1) (length bs2); bs = bin_to_bl len (sbl_to_bin bs1 - sbl_to_bin bs2)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Sig bs)"

\<comment> \<open>unsigned left shift\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs);  bs' = drop n (bs @ replicate n False)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Uns bs')"

\<comment> \<open>signed left shift\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs);  bs' = drop n (bs @ replicate n False)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Sig bs')"

\<comment> \<open>unsigned right shift\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs);  bs' = take (length bs) (replicate n False @ bs)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Uns bs')"

\<comment> \<open>signed right shift\<close>
| "\<lbrakk>beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs);  bs' = take (length bs) (replicate n (hd bs) @ bs)\<rbrakk>
                                              \<Longrightarrow>  beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Sig bs')"

\<comment> \<open>conditional expression true\<close>
| "beval_raw now \<sigma> \<gamma> \<theta> def guard (Bv True) \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def th res \<Longrightarrow>
                                                    beval_raw now \<sigma> \<gamma> \<theta> def (Bwhen th guard el) res"

\<comment> \<open>conditional expression false\<close>
| "beval_raw now \<sigma> \<gamma> \<theta> def guard (Bv False) \<Longrightarrow> beval_raw now \<sigma> \<gamma> \<theta> def el res \<Longrightarrow>
                                                    beval_raw now \<sigma> \<gamma> \<theta> def (Bwhen th guard el) res"

| "beval_raw now \<sigma> \<gamma> \<theta> def (Bliteral sign val) (Lv sign val)"

inductive_cases beval_cases[elim!]:
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig sig) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Btrue) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bfalse) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig_delayed sig dly) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig_event sig) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bnot e) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Band e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bor e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bnand e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bnor e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bxor e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bxnor e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bslice sig l r) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bindex sig idx) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Badd e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bmult e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsub e1 e2) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bshiftl e n) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bshiftr e n) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bwhen th g el) \<longrightarrow>\<^sub>b res"
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bliteral sign val) \<longrightarrow>\<^sub>b res"

inductive_cases beval_cases2:
  "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b res"

lemma [simp]:
  "(\<lambda>x y. (x \<or> y) \<and> x = (\<not> y)) = xor"
  using less_le by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Uns bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2)
                   \<and> length bs = max (length bs1) (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Badd e1 e2) (Lv Sig bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2)
                   \<and> length bs = max (length bs1) (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Uns bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2)
                   \<and> length bs = max (length bs1) (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bsub e1 e2) (Lv Sig bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2)
                   \<and> length bs = max (length bs1) (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bmult e1 e2)(Lv Uns bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Uns bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Uns bs2)
                   \<and> length bs = (length bs1) + (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bmult e1 e2)(Lv Sig bs)"
  shows   "\<exists>bs1 bs2. beval_raw now \<sigma> \<gamma> \<theta> def e1 (Lv Sig bs1)
                   \<and> beval_raw now \<sigma> \<gamma> \<theta> def e2 (Lv Sig bs2)
                   \<and> length bs = (length bs1) + (length bs2)"
  using assms size_bin_to_bl_aux by fastforce

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Uns bs)"
  shows   "\<exists>bs'. beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs') \<and> length bs' = length bs"
  by (rule beval_cases(18)[OF assms])
     (fastforce, blast)

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Sig bs)"
  shows   "\<exists>bs'. beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs') \<and> length bs' = length bs"
  by (rule beval_cases(18)[OF assms])
     (blast, fastforce)

lemma shift_left_amount_too_large_unsigned:
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs')"
  assumes "n \<ge> length bs'"
  shows   "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Uns (replicate (length bs') False))"
  using assms
  by (smt append_self_conv2 beval_raw.intros(28) diff_diff_cancel drop_append drop_eq_Nil drop_replicate)

lemma shift_left_amount_too_large_signed:
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs')"
  assumes "n \<ge> length bs'"
  shows   "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftl e n) (Lv Sig (replicate (length bs') False))"
  using assms
  by (smt append_self_conv2 beval_raw.intros(29) diff_diff_cancel drop_append drop_eq_Nil drop_replicate)

lemma shift_right_amount_too_large_unsigned:
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs')"
  assumes "n \<ge> length bs'"
  shows   "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Uns (replicate (length bs') False))"
  using assms
  by (smt append_Nil2 beval_raw.intros(30) diff_is_0_eq' length_replicate min.orderE take0
  take_append take_replicate)

lemma shift_right_amount_too_large_signed:
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs')"
  assumes "n \<ge> length bs'"
  shows   "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Sig (replicate (length bs') (hd bs')))"
  using assms
  by (smt append.right_neutral beval_raw.intros(31) diff_is_0_eq' length_replicate min.orderE take0
  take_append take_replicate)

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Uns bs)"
  shows   "\<exists>bs'. beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Uns bs') \<and> length bs' = length bs"
  by (rule beval_cases(19)[OF assms])
     (fastforce, blast)

lemma
  assumes "beval_raw now \<sigma> \<gamma> \<theta> def (Bshiftr e n) (Lv Sig bs)"
  shows   "\<exists>bs'. beval_raw now \<sigma> \<gamma> \<theta> def e (Lv Sig bs') \<and> length bs' = length bs"
  by (rule beval_cases(19)[OF assms])
     (blast, fastforce)

lemma beval_raw_deterministic_weaker:
  assumes "now, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> e \<longrightarrow>\<^sub>b res1"
  assumes "now, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> e \<longrightarrow>\<^sub>b res2"
  assumes "\<forall>s k. k \<le> now \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows "res2 = res1"
  using assms
proof (induction arbitrary:res2 rule:beval_raw.induct)
  case (34 now \<sigma> \<gamma> \<theta> def sign val)
  then show ?case by blast
next
  case (32 now \<sigma> \<gamma> \<theta> def guard th res el)
  then show ?case by blast
next
  case (33 now \<sigma> \<gamma> \<theta> def guard el res th)
  then show ?case by blast
next
  case (21 now \<sigma> \<gamma> \<theta> def sig ki bs idx)
  then show ?case
    by (metis beval_cases(14) val.sel(3))
next
  case (17 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  then show ?case by auto blast
next
  case (20 now \<sigma> \<gamma> \<theta> def sig ki bs len l r)
  then show ?case
    by (metis Suc_eq_plus1 beval_cases(13) diff_diff_left val.sel(2) val.sel(3))
qed auto

lemma beval_raw_deterministic:
  assumes "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b res1"
  assumes "now, \<sigma>, \<gamma>, \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b res2"
  shows "res2 = res1"
  using beval_raw_deterministic_weaker assms by fastforce

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bsig sig) \<longrightarrow>\<^sub>b res"
  shows "res = \<sigma> sig"
  using assms by auto

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> Btrue \<longrightarrow>\<^sub>b res"
  shows "res = Bv True"
  using assms by auto

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> Bfalse \<longrightarrow>\<^sub>b res"
  shows "res = Bv False"
  using assms by auto

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b Bv (bool)"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> (Bnot e) \<longrightarrow>\<^sub>b res"
  shows "res = Bv (\<not> bool)"
  using assms  by (meson beval_raw.intros beval_raw_deterministic)

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

abbreviation post_necessary_raw :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" where
  "post_necessary_raw n \<tau> t s val def \<equiv> (signal_of def \<tau> s (t + n) \<noteq> val)"

lemma post_necessary_raw_correctness:
  "\<not> post_necessary_raw n \<tau> t s val def \<longleftrightarrow> (\<exists>i. i \<le> t + n \<and> \<tau> i s = Some val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None))
                                        \<or>   (\<forall>i. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val = def"
  using signal_of_val_eq[of "def" "\<tau>" "s" "t + n" "val"] unfolding to_trans_raw_sig_def by auto

lemma post_necessary_raw_correctness2:
  "post_necessary_raw n \<tau> t s val def \<longleftrightarrow> (\<exists>i val'. i \<le> t + n \<and> \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None))
                                      \<or>   (\<forall>i. i \<le> t + n \<longrightarrow> \<tau> i s = None) \<and> val \<noteq> def"
  (is "?lhs \<longleftrightarrow> (?rhs1 \<or> ?rhs2)")
proof
  assume "?rhs1 \<or> ?rhs2"
  moreover
  { assume "?rhs1"
    then obtain i val' where "i \<le> t + n" and "\<tau> i s = Some val'" and "val' \<noteq> val" and *: "\<forall>j > i. j \<le> t + n \<longrightarrow> \<tau> j s = None"
      by auto
    have "inf_time (to_trans_raw_sig \<tau>) s (t + n) = Some i"
    proof (rule inf_time_someI)
      show "i \<in> dom (to_trans_raw_sig \<tau> s)"
        by (simp add: \<open>\<tau> i s = Some val'\<close> domIff to_trans_raw_sig_def)
    next
      { fix ta
        assume "ta \<in> dom (to_trans_raw_sig \<tau> s)"
        assume "ta \<le> t + n"
        assume "\<not> ta \<le> i"
        hence "i < ta" by auto
        hence "\<tau> ta s = None"
          using * `ta \<le> t + n` by auto
        hence "ta \<notin> dom (to_trans_raw_sig \<tau> s)"
          by (simp add: domIff to_trans_raw_sig_def)
        hence False
          using \<open>ta \<in> dom (to_trans_raw_sig \<tau> s)\<close> by blast }
      thus "\<forall>ta\<in>dom (to_trans_raw_sig \<tau> s). ta \<le> t + n \<longrightarrow> ta \<le> i "
        by blast
    qed (auto simp add: `i \<le> t + n`)
    hence "signal_of def \<tau> s (t + n) = val'"
      using `\<tau> i s = Some val'` unfolding to_signal_def comp_def
      by (simp add: to_trans_raw_sig_def)
    hence "post_necessary_raw n \<tau> t s val def"
      using `val' \<noteq> val` by auto }
  moreover
  { assume "?rhs2"
    hence "inf_time (to_trans_raw_sig \<tau>) s (t + n) = None"
      by (metis (mono_tags, lifting) domIff inf_time_def keys_def mem_Collect_eq
      to_trans_raw_sig_def zero_option_def)
    hence "signal_of def \<tau> s (t + n) = def"
      by (simp add: to_signal_def)
    hence "post_necessary_raw n \<tau> t s val def"
      using `?rhs2` by auto }
  ultimately show "post_necessary_raw n \<tau> t s val def"
    by auto
next
  { assume "\<not> (?rhs1 \<or> ?rhs2)"
    hence "\<not> ?rhs1" and "\<not> ?rhs2" by auto
    have *: "\<forall>i val'. \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None) \<longrightarrow> i > t + n"
      using `\<not> ?rhs1`  using leI by blast
    have **: "(\<forall>i\<le>t + n. \<tau> i s = None) \<longrightarrow> val = def"
      using `\<not> ?rhs2` by blast
    have "(\<forall>i \<le> t + n. \<tau> i s = None) \<or> (\<exists>i \<le> t + n. \<tau> i s \<noteq> None)"
      by blast
    moreover
    { assume "\<forall>i \<le> t + n. \<tau> i s = None"
      hence "signal_of def \<tau> s (t + n) = def" and "val = def"
        using ** by (meson post_necessary_raw_correctness)+
      hence "\<not> post_necessary_raw n \<tau> t s val def"
        by blast }
    moreover
    { assume "\<exists>i \<le> t + n. \<tau> i s \<noteq> None"
      let ?i = "GREATEST i. i \<le> t + n \<and> \<tau> i s \<noteq> None"
      have "?i \<le> t + n" and "\<tau> ?i s \<noteq> None"
        using GreatestI_ex_nat[OF `\<exists>i \<le> t + n. \<tau> i s \<noteq> None`, where b= "t + n"]
        by auto
      have ***: "\<forall>j > ?i. j \<le> t + n \<longrightarrow> \<tau> j s = None"
        by (smt Greatest_le_nat add.commute leD)
      obtain val' where "\<tau> ?i s = Some val'"
        using \<open>\<tau> (GREATEST i. i \<le> t + n \<and> \<tau> i s \<noteq> None) s \<noteq> None\<close> by blast
      have "val' = val"
        using * "***" \<open>(GREATEST i. i \<le> t + n \<and> \<tau> i s \<noteq> None) \<le> t + n\<close> \<open>\<not> ((\<exists>i val'. i \<le> t + n \<and> \<tau>
        i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<le>t + n. \<tau> i s =
        None) \<and> val \<noteq> def)\<close> \<open>\<tau> (GREATEST i. i \<le> t + n \<and> \<tau> i s \<noteq> None) s = Some val'\<close> by blast
      have "inf_time (to_trans_raw_sig \<tau>) s (t + n) = Some ?i"
      proof (rule inf_time_someI)
        show "?i \<in> dom (to_trans_raw_sig \<tau> s)"
          by (metis (full_types) \<open>\<tau> (GREATEST i. i \<le> t + n \<and> \<tau> i s \<noteq> None) s \<noteq> None\<close> domIff
          to_trans_raw_sig_def)
      next
        { fix ta
          assume "ta \<in> dom (to_trans_raw_sig \<tau> s)"
          assume "ta \<le> t + n"
          assume "\<not> ta \<le> ?i"
          hence "?i < ta" by auto
          hence "\<tau> ta s = None"
            using ***  \<open>ta \<le> t + n\<close> by blast
          hence False
            by (metis \<open>ta \<in> dom (to_trans_raw_sig \<tau> s)\<close> domIff to_trans_raw_sig_def) }
        thus "\<forall>ta \<in> dom (to_trans_raw_sig \<tau> s). ta \<le> t + n \<longrightarrow> ta \<le> ?i"
          by auto
      next
        show "?i \<le> t + n"
          using `?i \<le> t + n` by auto
      qed
      hence "signal_of def \<tau> s (t + n) =  val"
        using `\<tau> ?i s = Some val'` `val' = val` unfolding to_signal_def comp_def
        by (simp add: to_trans_raw_sig_def)
      hence "\<not> post_necessary_raw n \<tau> t s val def"
        by blast }
    ultimately have "\<not> post_necessary_raw n \<tau> t s val def"
      by auto }
  thus "post_necessary_raw n \<tau> t s val def \<Longrightarrow>
    (\<exists>i val'. i \<le> t + n \<and> \<tau> i s = Some val' \<and> val' \<noteq> val \<and> (\<forall>j>i. j \<le> t + n \<longrightarrow> \<tau> j s = None)) \<or> (\<forall>i\<le>t + n. \<tau> i s = None) \<and> val \<noteq> def"
    by blast
qed

lemma post_necessary_raw_same:
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  shows "post_necessary_raw n \<tau>1 t s val def = post_necessary_raw n \<tau>2 t s val def"
  using assms   by (metis signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def)

definition trans_post_raw ::
  "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal trans_raw" where
  "trans_post_raw s val def \<tau> t dly =
      (if post_necessary_raw (dly - 1) \<tau> t s val def then
          post_raw s val \<tau> (t + dly)
       else
          preempt_raw s \<tau> (t + dly))"

lemma trans_post_raw_almost_all_zero:
  fixes \<tau> :: "nat \<Rightarrow> 'signal \<rightharpoonup> val"
  assumes " \<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. trans_post_raw s v def \<tau> t dly x = 0"
proof (cases "post_necessary_raw (dly - 1) \<tau> t s v def")
  case True
  then show ?thesis
    using assms unfolding trans_post_raw_def post_raw_def
    by (smt MOST_mono MOST_neq(2) MOST_rev_mp fun_upd_idem_iff zero_fun_def zero_option_def)
next
  case False
  then show ?thesis
    using assms unfolding trans_post_raw_def preempt_raw_def
    by (simp add: MOST_mono zero_fun_def zero_option_def)
qed

lemma trans_post_raw_imply_neq_map_empty:
  assumes "\<tau>' =  trans_post_raw sig e def \<tau> t dly"
  assumes "(\<forall>i. i \<le> t + (dly-1) \<longrightarrow> \<tau> i sig = None) \<Longrightarrow> e \<noteq> def"
  assumes "0 < dly"
  shows "\<tau>' \<noteq> 0"
proof (cases "post_necessary_raw (dly - 1) \<tau> t sig e def ")
  case True
  then show ?thesis
    using assms unfolding trans_post_raw_def
    by (metis fun_upd_apply option.distinct(1) post_raw_def zero_fun_def zero_option_def)
next
  case False
  hence *: "(\<exists>i. i \<le> t + (dly-1) \<and> \<tau> i sig = Some e \<and> (\<forall>j>i. j \<le> t + (dly-1) \<longrightarrow> \<tau> j sig = None))"
    unfolding post_necessary_raw_correctness using assms(2) by blast
  hence lookup: "\<tau>' =  preempt_raw sig \<tau> (t + dly)"
    using assms(1) False  by (simp add: trans_post_raw_def)
  obtain i where "i \<le> t + (dly - 1)" and "\<tau> i sig = Some e"
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
  by (smt assms inf_time_at_most le_less_trans option.case_eq_if option.collapse trans_post_less)

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
    then obtain t' where "t' \<le> k + (dly-1) \<and>  \<tau> t' s = Some v \<and> (\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)
                       \<or> (\<forall>j. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None) \<and> v = def"
      using post_necessary_raw_correctness[of "def" "\<tau>" "s" "k" "dly - 1" "v"] by auto
    moreover
    { assume "t' \<le> k + (dly-1) \<and>  \<tau> t' s = Some v \<and> (\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)"
      hence "t' \<le> k + (dly-1)" and " \<tau> t' s = Some v" and "(\<forall>j>t'. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None)"
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
    { assume "(\<forall>j. j \<le> k + (dly-1) \<longrightarrow> \<tau> j s = None) \<and> v = def"
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
            using `(\<forall>j. j \<le> k + (dly-1) \<longrightarrow>  \<tau> j s = None) \<and> v = def` as_not
            by (auto simp add: to_trans_raw_sig_def trans_post_raw_def preempt_raw_def zero_option_def)
          with ` (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta \<noteq> 0` have "False" by auto }
        moreover
        { assume "k + dly < ta"
          hence " (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta = 0"
            using as_not  unfolding to_trans_raw_sig_def
            by (metis as_not fun_upd_same less_imp_le_nat preempt_raw_def trans_post_raw_def zero_option_def)
          with ` (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly) s) ta \<noteq> 0` have "False" by auto }
        ultimately show "False"by auto
      qed
      hence "inf_time (to_trans_raw_sig (trans_post_raw s v def \<tau> k dly)) s t = None"
        by (auto simp add: inf_time_none_iff)
      hence ?thesis
        unfolding to_signal_def comp_def using `(\<forall>j. j \<le> k + (dly-1) \<longrightarrow> \<tau> j s = None) \<and> v = def`
        by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis
    by auto
qed

fun check :: "('signal \<rightharpoonup> val) \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool" where
  "check \<sigma> sig val = (case \<sigma> sig of None \<Rightarrow> True | Some val' \<Rightarrow> val = val')"

definition combine_trans_bit :: "'signal trans_raw \<Rightarrow> (val \<times> 'signal trans_raw) list \<Rightarrow> signedness \<Rightarrow> 'signal \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal trans_raw" where
  "combine_trans_bit base d\<tau> sign sig' t dly = (let kset = fold (\<union>) (map (keys o (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig') o snd) d\<tau>) {} in 
                                               (\<lambda>n sig. if n \<le> t \<or> n > t + dly \<or> sig \<noteq> sig' then base n sig else 
                                                        if n \<in> kset then Some (Lv sign (map (\<lambda>p. bval_of (signal_of (fst p) (snd p) sig n)) d\<tau>)) else None))"

definition purge_raw :: "'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw" where
  "purge_raw \<tau> t dly sig def val \<equiv>
    let
        s1 = signal_of def \<tau> sig t;
        s2 = signal_of def \<tau> sig (t + dly);
        k2 = inf_time (to_trans_raw_sig \<tau>) sig (t + dly)
    in
        if s1 = val \<or> s2 \<noteq> val then
          override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t <.. t + dly}
        else
          override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t <..< the k2} \<union> {the k2 <.. t + dly})"

lemma purge_raw_neq_0_imp:
  assumes "purge_raw \<tau> t dly sig def val k sig \<noteq> 0"
  assumes "t < k" and "k < t + dly"
  shows   "inf_time (to_trans_raw_sig \<tau>) sig (t + dly) = Some k \<and> signal_of def \<tau> sig t \<noteq> val \<and> signal_of def \<tau> sig (t + dly) = val"
proof -
  let ?s1 = "signal_of def \<tau> sig t"
  let ?s2 = "signal_of def \<tau> sig (t + dly)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (t + dly)"

  have "(?s1 = val \<or> ?s2 \<noteq> val) \<or> (?s1 \<noteq> val \<and> ?s2 = val)"
    by auto
  moreover
  { assume "?s1 = val \<or> ?s2 \<noteq> val"
    hence "purge_raw \<tau> t dly sig def val k sig = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {t <.. t + dly} k sig"
      unfolding purge_raw_def Let_def by auto
    also have "... = 0"
      using `t < k` `k < t + dly`  by (simp add: zero_option_def)
    finally have False
      using assms by auto
    hence ?thesis
      by auto }
  moreover
  { assume "?s1 \<noteq> val \<and> ?s2 = val"
    hence "override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({t <..< the ?k2} \<union> {the ?k2 <.. t + dly}) k sig \<noteq> 0"
      using assms unfolding purge_raw_def Let_def by auto
    hence "the ?k2 = k"
      using `t < k` `k < t + dly` 
      by (metis (mono_tags) UnCI fun_upd_same greaterThanAtMost_iff greaterThanLessThan_iff less_imp_le nat_neq_iff override_on_apply_in zero_option_def)
    hence ?thesis
      by (metis (mono_tags, lifting) \<open>signal_of def \<tau> sig t \<noteq> val \<and> signal_of def \<tau> sig (t + dly) =
      val\<close> inf_time_none_iff less_le_trans not_add_less1 not_le_imp_less o_def option.collapse
      to_signal_def) }
  ultimately show ?thesis
    by auto
qed

definition purge_raw' :: "'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw" where
  "purge_raw' \<tau> t dly sig def val \<equiv> (case val of Bv b       \<Rightarrow> purge_raw \<tau> t dly sig def val 
                                               | Lv sign bs \<Rightarrow> combine_trans_bit \<tau> (zip (map (\<lambda>n. (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n))) [0..< length bs]) 
                                                                                   (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau> n sig) t dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..< length bs])) sign sig t dly)"

lemma purge_raw_induct:
  "\<And>m. now + Suc n \<le> m \<Longrightarrow> purge_raw \<tau> now n sig def val m = \<tau> m"
proof -
  have 0: "\<And>m. now + Suc n \<le> m \<Longrightarrow> override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {now <.. now + n} m = \<tau> m"
    by auto
  let ?s1 = "signal_of def \<tau> sig now"
  let ?s2 = "signal_of def \<tau> sig (now + n)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (now + n)"
  { assume "?s1 \<noteq> val \<and> ?s2 = val"
    hence "?s1 \<noteq> val" and "?s2 = val"
      by auto
    hence *: "\<exists>k\<in> keys(to_trans_raw_sig \<tau> sig). k \<le> now + n"
      by (metis (no_types, lifting) inf_time_def inf_time_none_iff le_add1 le_less_trans o_apply to_signal_def)
    hence "?k2 = Some (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)" (is "_ = Some ?k2'")
      unfolding inf_time_def by auto
    hence "?k2' \<le> now + n"
      using GreatestI_ex_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> now + n" and b="now + n"]
      * by auto
    hence "\<And>m. now + Suc n \<le> m \<Longrightarrow> override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({now <..< the ?k2} \<union> {the ?k2 <.. now + n}) m = \<tau> m"
      using \<open>inf_time (to_trans_raw_sig \<tau>) sig (now + n) = Some (GREATEST k. k \<in> keys
      (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)\<close> by auto }
  with 0 show "\<And>m. now + Suc n \<le> m \<Longrightarrow> purge_raw \<tau> now n sig def val m = \<tau> m"
    unfolding purge_raw_def by smt
qed

lemma purge_raw_induct':
  "purge_raw \<tau> now n sig def val = \<tau>' \<Longrightarrow>  \<tau>' (now + Suc n) = \<tau> (now + Suc n)"
  using purge_raw_induct[of "now" "n" "now + Suc n" "\<tau>"] by auto

lemma purge_raw_before_now_unchanged:
  assumes "purge_raw \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m. m \<le> now \<longrightarrow> \<tau> m =  \<tau>' m"
proof (rule, rule)
  fix m
  assume "m \<le> now"
  hence 0: "\<tau> m = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {now <.. now + n} m"
    by simp
  let ?s1 = "signal_of def \<tau> sig now"
  let ?s2 = "signal_of def \<tau> sig (now + n)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (now + n)"
  { assume "?s1 \<noteq> val \<and> ?s2 = val"
    hence *: "\<exists>k\<in> keys(to_trans_raw_sig \<tau> sig). k \<le> now + n"
      by (smt add.commute comp_apply inf_time_ex2 to_signal_def trans_le_add2)
    hence "?k2 = Some (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)" (is "_ = Some ?k2'")
      unfolding inf_time_def by auto
    have "?k2' \<in> keys (to_trans_raw_sig \<tau> sig)"
      using GreatestI_ex_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> now + n" and b="now + n"]
      * by auto
    hence **: "\<And>m. m > ?k2' \<Longrightarrow> m \<le> now + n \<Longrightarrow> m \<notin> keys (to_trans_raw_sig \<tau> sig)"
      using Greatest_le_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> now + n" and b= "now + n"]
      using leD by blast
    hence "\<tau> (the ?k2) sig = Some val"
      using \<open>?s1 \<noteq> val \<and> ?s2 = val\<close> \<open>?k2 = Some ?k2'\<close> \<open>?k2' \<in> keys (to_trans_raw_sig \<tau> sig)\<close>
      unfolding to_signal_def comp_def to_trans_raw_sig_def
      by (smt domI domIff keys_def mem_Collect_eq option.case_eq_if option.collapse option.sel zero_option_def)
    have "now \<le> ?k2'"
    proof (rule ccontr)
      assume "\<not> now \<le> ?k2'"
      hence "?k2' < now"
        by auto
      hence ***: "\<And>m. m > ?k2' \<Longrightarrow> m \<le> now \<Longrightarrow> \<tau> m sig = None"
        using **
        by (simp add: keys_def to_trans_raw_sig_def zero_option_def)
      have "inf_time (to_trans_raw_sig \<tau>) sig now = Some ?k2'"
      proof (intro inf_time_someI)
        show "?k2' \<in> dom (to_trans_raw_sig \<tau> sig)"
          using \<open>?k2' \<in> keys (to_trans_raw_sig \<tau> sig)\<close>  by (simp add: dom_def keys_def zero_option_def)
      next
        show "?k2' \<le> now"
          using \<open>?k2' < now\<close> by auto
      next
        show "\<forall>t\<in>dom (to_trans_raw_sig \<tau> sig). t \<le> now \<longrightarrow> t \<le> ?k2'"
          using ***
          by (metis \<open>inf_time (to_trans_raw_sig \<tau>) sig (now + n) = Some (GREATEST k. k \<in> keys
          (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)\<close> add_leD1 inf_time_someE le_Suc_ex le_add1)
      qed
      hence "?s1 = val"
        unfolding to_signal_def comp_def using \<open>\<tau> (the ?k2) sig = Some val\<close>
        by (metis \<open>inf_time (to_trans_raw_sig \<tau>) sig (now + n) = Some (GREATEST k. k \<in> keys
        (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)\<close> \<open>signal_of def \<tau> sig now \<noteq> val \<and> signal_of def \<tau>
        sig (now + n) = val\<close> comp_def to_signal_def)
      with \<open>?s1 \<noteq> val \<and> ?s2 = val\<close> show False
        by auto
    qed
    hence "\<tau> m = override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({now <..< the ?k2} \<union> {the ?k2 <.. now + n}) m"
      using \<open>?k2 = Some ?k2'\<close>  using \<open>m \<le> now\<close> by auto }
  with 0 show "\<tau> m = \<tau>' m"
    using assms unfolding purge_raw_def  by smt
qed

lemma purge_raw'_before_now_unchanged:
  assumes "purge_raw' \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m. m \<le> now \<longrightarrow> \<tau> m =  \<tau>' m"
  using assms
proof (induction val)
  case (Bv x)
  then show ?case 
    using purge_raw_before_now_unchanged 
  proof -
    { fix nn :: nat
      have "(case Bv x of Bv b \<Rightarrow> purge_raw \<tau> now n sig def (Bv x) | Lv s bs \<Rightarrow> combine_trans_bit \<tau> (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (lval_of def ! na)) (Bv (bs ! na))) [0..<length bs])) s sig now n) = \<tau>'"
        using Bv.prems unfolding purge_raw'_def by auto
      then have "\<not> nn \<le> now \<or> \<tau>' nn = \<tau> nn"
        by (metis purge_raw_before_now_unchanged val.simps(5)) }
    then show ?thesis
      by simp
  qed
next
  case (Lv sign bs)
  hence \<tau>'_def: "\<tau>' =  combine_trans_bit \<tau>
        (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) 
             (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! na)) (Bv (bs ! na))) [0..<length bs])) sign sig
        now n"
    unfolding purge_raw'_def by auto  
  then show ?case 
    unfolding combine_trans_bit_def by auto
qed

lemma member_fold_union:
  assumes "m \<in> fold (\<union>) xs init"
  shows   "m \<in> init \<or> (\<exists>x \<in> set xs. m \<in> x)"
  using assms
proof (induction xs arbitrary: init)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  hence "m \<in> fold (\<union>) (xs) (a \<union> init)"
    by auto
  hence "m \<in> (a \<union> init) \<or> (\<exists>a\<in>set xs. m \<in> a)"
    using Cons by auto
  then show ?case 
    by auto
qed

lemma member_fold_union':
  assumes   "m \<in> init \<or> (\<exists>x \<in> set xs. m \<in> x)"
  shows     "m \<in> fold (\<union>) xs init"
  using assms
proof (induction xs arbitrary: init)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    using set_ConsD by auto
qed

lemma member_fold_union2: 
  "m \<in> fold (\<union>) xs init \<longleftrightarrow> m \<in> init \<or> (\<exists>x \<in> set xs. m \<in> x)"
  by (meson member_fold_union member_fold_union')

lemma purge_raw_before_now_unchanged':
  assumes "purge_raw' \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m. m \<le> now  \<longrightarrow> \<tau> m =  \<tau>' m"
  using assms
proof (induction val)
  case (Bv x)
  then show ?case 
    unfolding purge_raw'_def  using purge_raw_before_now_unchanged  by (metis val.simps(5))
next
  case (Lv sign bs)
  hence *: "combine_trans_bit \<tau>
        (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
          (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! na)) (Bv (bs ! na))) [0..<length bs]))
        sign sig now n = \<tau>'"
    unfolding purge_raw'_def by auto
  { fix m :: nat
    fix s
    assume "m \<le> now"
    hence **: "\<tau>' m = combine_trans_bit \<tau>
        (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
          (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! na)) (Bv (bs ! na))) [0..<length bs]))
        sign sig now n m"
      using * by auto
    \<comment> \<open>calculation\<close>
    have calc: "(map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> snd)
                     (zip (map (\<lambda>n. Bv (lval_of def ! n)) [0..<length bs])
                       (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (lval_of def ! na)) (Bv (bs ! na))) [0..<length bs]))) =
          (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> sig) \<circ> (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (lval_of def ! na)) (Bv (bs ! na))))
                        [0..<length bs])"
      unfolding sym[OF map_map]  map_snd_zip_take length_map min.idem length_upt 
      using take_all by auto
    hence "\<tau>' m s = combine_trans_bit \<tau>
      (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
        (map (\<lambda>na. purge_raw (to_trans_raw_bit def \<tau> na sig) now n sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! na)) (Bv (bs ! na))) [0..<length bs]))
      sign sig now n m s"
      using ** by auto
    also have "... = \<tau> m s"
      unfolding combine_trans_bit_def using `m \<le> now` unfolding Let_def by auto
    finally have "\<tau>' m s = \<tau> m s"
      by auto }
  thus ?case
    by (intro allI, intro impI, intro ext) auto
qed

lemma purge_raw_after_delay_unchanged:
  assumes "purge_raw \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m. now + n < m \<longrightarrow> \<tau> m = \<tau>' m"
  using assms purge_raw_induct  by (metis Suc_leI add_Suc_right)

lemma purge_raw_does_not_affect_other_sig:
  assumes "purge_raw \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  using assms
  by (smt fun_upd_other override_on_apply_in override_on_apply_notin purge_raw_def)

lemma purge_raw_does_not_affect_other_sig':
  assumes "purge_raw' \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  using assms
  unfolding purge_raw'_def 
  by (auto split:val.splits simp add: purge_raw_does_not_affect_other_sig combine_trans_bit_def)

lemma purge_raw_correctness:
  assumes "purge_raw \<tau> now n sig def val = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> check (\<tau>' m) sig val"
proof (rule, rule)
  fix m
  assume "now < m \<and> m \<le> now + n"
  have 0: "check (override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {now <.. now + n} m) sig val"
    by (simp add: \<open>now < m \<and> m \<le> now + n\<close>)
  let ?s1 = "signal_of def \<tau> sig now"
  let ?s2 = "signal_of def \<tau> sig (now + n)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (now + n)"
  { assume "?s1 \<noteq> val \<and> ?s2 = val"
    hence "?s1 \<noteq> val" and "?s2 = val"
      by auto
    hence *: "\<exists>k\<in> keys(to_trans_raw_sig \<tau> sig). k \<le> now + n"
      by (smt add.commute comp_apply inf_time_ex2 to_signal_def trans_le_add2)
    hence "?k2 = Some (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau> sig) \<and> k \<le> now + n)" (is "_ = Some ?k2'")
      unfolding inf_time_def by auto
    have "?k2' \<in> keys (to_trans_raw_sig \<tau> sig)"
      using GreatestI_ex_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> now + n" and b="now + n"]
      * by auto
    hence **: "\<And>m. m > ?k2' \<Longrightarrow> m \<le> now + n \<Longrightarrow> m \<notin> keys (to_trans_raw_sig \<tau> sig)"
      using Greatest_le_nat[where P="\<lambda>x. x \<in> keys (to_trans_raw_sig \<tau> sig) \<and> x \<le> now + n" and b= "now + n"]
      using leD by blast
    hence "\<tau> (the ?k2) sig = Some val"
      using \<open>?s2 = val\<close> \<open>?k2 = Some ?k2'\<close> \<open>?k2' \<in> keys (to_trans_raw_sig \<tau> sig)\<close>
      unfolding to_signal_def comp_def to_trans_raw_sig_def
      by (smt domI domIff keys_def mem_Collect_eq option.case_eq_if option.collapse option.sel zero_option_def)
    hence "check (override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({now <..< the ?k2} \<union> {the ?k2 <.. now + n}) m) sig val"
      using \<open>now < m \<and> m \<le> now + n\<close>
    proof -
      have "check (override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({now<..<the (inf_time (to_trans_raw_sig \<tau>) sig (now + n))} \<union> {the (inf_time (to_trans_raw_sig \<tau>) sig (now + n))<..now + n}) m) sig val \<or> m \<in> {now<..<the (inf_time (to_trans_raw_sig \<tau>) sig (now + n))} \<union> {the (inf_time (to_trans_raw_sig \<tau>) sig (now + n))<..now + n} \<and> check ((\<tau> m)(sig := None)) sig val"
        using \<open>\<tau> (the (inf_time (to_trans_raw_sig \<tau>) sig (now + n))) sig = Some val\<close> \<open>now < m \<and> m \<le> now + n\<close> by force
      then show ?thesis
        by force
    qed }
  with 0 show "check (\<tau>' m) sig val"
    by (smt assms override_on_def purge_raw_def)
qed

text \<open>This is the function for posting a transaction in an inertial assignment statement.\<close>

definition inr_post_raw :: "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat
                                                                             \<Rightarrow> 'signal trans_raw" where
  "inr_post_raw sig val def \<tau> now dly = trans_post_raw sig val def (purge_raw \<tau> now dly sig def val) now dly"

definition inr_post_raw' :: "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat
                                                                             \<Rightarrow> 'signal trans_raw" where
  "inr_post_raw' sig val def \<tau> now dly = trans_post_raw sig val def (purge_raw' \<tau> now dly sig def val) now dly"

lemma inr_post_raw'_eq_inr_post_raw:
  "inr_post_raw' sig (Bv v) def \<tau> now dly = inr_post_raw sig (Bv v) def \<tau> now dly"
  unfolding inr_post_raw'_def inr_post_raw_def purge_raw'_def
  by (auto)
   
lemma inr_post_raw_does_not_affect_other_sig:
  fixes dly \<tau> now def val sig
  defines "\<tau>' \<equiv> inr_post_raw sig val def \<tau> now dly"
  shows " \<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  by (metis assms inr_post_raw_def purge_raw_does_not_affect_other_sig to_trans_raw_sig_def trans_post_raw_diff_sig)

lemma inr_post_raw_does_not_affect_other_sig':
  fixes dly \<tau> now def val sig
  defines "\<tau>' \<equiv> inr_post_raw' sig val def \<tau> now dly"
  shows " \<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  by (metis assms inr_post_raw'_def purge_raw_does_not_affect_other_sig' to_trans_raw_sig_def trans_post_raw_diff_sig)

lemma purge_raw_almost_all_zero:
  assumes "\<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. (purge_raw \<tau> now dly sig def val) x = 0"
proof -
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) sig (now + dly)"
  have "\<forall>\<^sub>\<infinity>x. override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) {now <.. now + dly} x = 0"
    using assms  by (simp add: MOST_mono override_on_def zero_fun_def zero_option_def)
  moreover have "\<forall>\<^sub>\<infinity>x. override_on \<tau> (\<lambda>n. (\<tau> n)(sig := None)) ({now <..< the ?k2} \<union> {the ?k2 <.. now + dly}) x = 0"
    using assms  by (simp add: eventually_mono override_on_def zero_fun_def zero_option_def)
  ultimately show ?thesis
    unfolding purge_raw_def Let_def by auto
qed

lemma combine_trans_bit_almost_all_zero:
  fixes f :: "nat \<Rightarrow> 'signal \<Rightarrow> val option"
  assumes "\<forall>\<^sub>\<infinity>x. f x = 0"
  assumes "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) list"
  shows   "\<forall>\<^sub>\<infinity>x. combine_trans_bit f list signedness signal now dly x = 0"
  unfolding combine_trans_bit_def Let_def 
proof -
  have "(\<lambda>x sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig
                 else if x \<in> fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {}
                 then Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (fst p) (snd p) sig x)) list)) else None) = 
        (override_on (\<lambda>x. if x \<le> now \<or> now + dly < x then f x else (f x)(signal := None)) 
                     (\<lambda>x. \<lambda>sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig else 
                               Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (fst p) (snd p) sig x)) list))) 
                     (fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {}))"
      (is "?fun = ?fun'") by (auto intro!: ext)
  have "finite {x. ?fun' x \<noteq> 0}"
    unfolding sym[OF eventually_cofinite] 
  proof (intro upd_eventually_cofinite_override_on_finite)
    have "\<And>init. finite init \<Longrightarrow> finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) list) init)"
      using assms(2)
    proof (induction list)
      case Nil
      then show ?case by auto
    next
      case (Cons a ps)
      have "pred_prod (\<lambda>a. True) (\<lambda>f. finite {x. f x \<noteq> 0}) a"
        using Cons(3) by auto
      hence "finite {x. snd a x \<noteq> 0}"
        using pred_prod_inject surjective_pairing[of "a"] by metis
      have **: " (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) (a # ps)) init) = 
             fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) ps) ({k. to_trans_raw_sig (snd a) signal k \<noteq> 0} \<union> init)"
        unfolding list.map(2) fold_Cons comp_def Un_empty_right by auto
      have "finite  ({k. to_trans_raw_sig (snd a) signal k \<noteq> 0} \<union> init)"
        using `finite init` `finite {x. snd a x \<noteq> 0}` unfolding finite_Un 
        to_trans_raw_sig_def
        by (metis (mono_tags, lifting) finite_nat_iff_bounded mem_Collect_eq subset_eq zero_fun_def)
      thus ?case
        using Cons by auto
    qed
    hence fin: "finite (fold (\<union>) (map (\<lambda>x. {k. to_trans_raw_sig (snd x) signal k \<noteq> 0}) list) {})"
      by auto
    thus " finite (fold (\<union>) (map (Femto_VHDL_raw.keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {})"
      unfolding keys_def comp_def by auto
  next
    show " \<forall>\<^sub>\<infinity>x. (if x \<le> now \<or> now + dly < x then f x else (f x)(signal := None)) = 0"
      using `\<forall>\<^sub>\<infinity>x. f x = 0`  by (simp add: MOST_mono zero_fun_def zero_option_def)
  qed
  thus "\<forall>\<^sub>\<infinity>x. (\<lambda>sig. if x \<le> now \<or> now + dly < x \<or> sig \<noteq> signal then f x sig
                  else if x \<in> fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> signal) \<circ> snd) list) {} then Some (Lv signedness (map (\<lambda>p. bval_of (signal_of (fst p) (snd p) sig x)) list))
                       else None) =
           0"
    unfolding sym[OF eventually_cofinite] 
    using `?fun = ?fun'` by metis
qed

lemma to_trans_raw_bit_almost_all_zero:
  assumes "\<forall>\<^sub>\<infinity>x. f x = 0"
  shows   "\<forall>\<^sub>\<infinity>x. to_trans_raw_bit def f n sig x = 0"
  using assms unfolding to_trans_raw_bit_alt_def 
  apply (intro upd_eventually_cofinite_override_on_finite)
  unfolding to_trans_raw_sig_def keys_def sym[OF eventually_cofinite]
  by (simp add: MOST_mono zero_fun_def)

lemma purge_raw_almost_all_zero':
  assumes "\<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. (purge_raw' \<tau> now dly sig def val) x = 0"
  using assms
proof (induction val)
  case (Bv x)
  then show ?case 
    unfolding purge_raw'_def by (auto simp add: purge_raw_almost_all_zero)
next
  case (Lv sign bs)
  have "purge_raw' \<tau> now dly sig def (Lv sign bs) = combine_trans_bit \<tau>
          (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau> n sig) now dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) 
          sign sig now dly"
    unfolding purge_raw'_def by auto
  have "list_all (pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0})) (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau> n sig) now dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))"
    unfolding list.pred_set
  proof
    fix x 
    assume "x \<in> set (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs])
                   (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau> n sig) now dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) "
    then obtain n where "n \<in> set [0 ..< length bs]" and "snd x = purge_raw (to_trans_raw_bit def \<tau> n sig) now dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))"
      by (smt in_set_zip length_map nth_map nth_mem)
    thus " pred_prod top (\<lambda>f. finite {x. f x \<noteq> 0}) x"
      using to_trans_raw_bit_almost_all_zero purge_raw_almost_all_zero assms 
    proof -
      have "\<forall>\<^sub>\<infinity>n. snd x n = 0"
        by (simp add: \<open>snd x = purge_raw (to_trans_raw_bit def \<tau> n sig) now dly sig (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))\<close> assms purge_raw_almost_all_zero to_trans_raw_bit_almost_all_zero)
      then show ?thesis
        by (metis (no_types) eventually_cofinite pred_prod_inject prod.collapse top_apply top_bool_def)
    qed
  qed
  thus ?case
    using assms unfolding purge_raw'_def
    by (simp add: combine_trans_bit_almost_all_zero)
qed

lemma signal_of_inr_post_before_now:
  assumes "n < now"
  assumes "\<forall>i < now. \<tau> i = 0"
  shows "signal_of def (inr_post_raw s v c \<tau> now dly) s n = def"
proof -
  have "\<forall>t \<le> n. inr_post_raw s v c \<tau> now dly t = 0"
    using assms(2)
    by (smt add_leE assms(1) inr_post_raw_def le_Suc_ex nat_less_le not_less post_raw_def
    preempt_raw_def purge_raw_before_now_unchanged trans_post_raw_def)
  hence "\<forall>t \<in> dom (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s). n < t"
    by (metis domIff not_less to_trans_raw_sig_def zero_fun_def zero_option_def)
  hence " inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s n = None"
    unfolding sym[OF inf_time_none_iff] by auto
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

lemma inr_post_raw_almost_all_zero:
  assumes "\<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. inr_post_raw sig val def \<tau> now dly x = 0"
proof -
  have **: "\<forall>\<^sub>\<infinity>x. (purge_raw \<tau> now dly sig def val) x = 0"
    using purge_raw_almost_all_zero[OF assms] by auto
  thus ?thesis
    unfolding inr_post_raw_def using trans_post_raw_almost_all_zero[OF **] by auto
qed

lemma inr_post_raw_almost_all_zero':
  assumes "\<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. inr_post_raw' sig val def \<tau> now dly x = 0"
proof -
  have **: "\<forall>\<^sub>\<infinity>x. (purge_raw' \<tau> now dly sig def val) x = 0"
    using purge_raw_almost_all_zero'[OF assms] by auto
  thus ?thesis
    unfolding inr_post_raw'_def using trans_post_raw_almost_all_zero[OF **] by auto
qed

lemma inr_post_purged:
  shows "\<And>n. now < n \<Longrightarrow> n \<le> now + dly \<Longrightarrow>
                                     (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                  \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
proof -
  fix n
  assume "now < n" and "n \<le> now + dly"
  hence "n < now + dly \<or> n = now + dly"
    by auto
  moreover
  { assume "n < now + dly"
    have "inr_post_raw sig val (\<sigma> sig) \<tau> now dly = trans_post_raw sig val (\<sigma> sig) (purge_raw \<tau> now dly sig (\<sigma> sig) val) now dly"
        (is "?inr = ?trans") unfolding inr_post_raw_def by auto
    hence "?inr n sig =  ?trans n sig"
      by auto
    also have "... =  (purge_raw \<tau> now dly sig (\<sigma> sig) val) n sig" (is "_ =  ?purge_raw n sig")
      using `n < now + dly`  by (metis to_trans_raw_sig_def trans_post_less)
    finally have " ?inr n sig =  ?purge_raw n sig"
      by auto
    moreover have " ?purge_raw n sig = None \<or>  ?purge_raw n sig = Some val"
      using purge_raw_correctness[of "\<tau>" "now" "dly" "sig" "\<sigma> sig" "val" "purge_raw \<tau> now dly sig (\<sigma>
      sig) val"] `now < n` `n < now + dly` using case_optionE by fastforce
    ultimately have " ?inr n sig = None \<or>  ?inr n sig = Some val"
      by auto
    hence " inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = Some val  \<or> inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = None"
      by linarith }
  moreover
  { assume "n = now + dly"
    hence " inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = Some val  \<or> inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = None"
      unfolding inr_post_raw_def trans_post_raw_def post_raw_def preempt_raw_def by auto }
  ultimately show "inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = Some val  \<or> inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = None"
    by auto
qed

lemma inr_post_purged':
  assumes "\<tau> now = 0"
  shows "\<And>n. now \<le> n \<Longrightarrow> n \<le> now + dly \<Longrightarrow>
                                     (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                  \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
proof -
  fix n
  assume "now \<le> n"
  assume "n \<le> now + dly"
  hence "n < now + dly \<or> n = now + dly"
    by auto
  moreover
  { assume "n < now + dly"

    have "now = n \<or> now < n"
      using `now \<le> n` by auto
    moreover
    { assume "now < n"
      hence "(inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                    \<or>   (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
        using inr_post_purged[OF `now < n` less_imp_le[OF `n < now + dly`]] by metis }
    moreover
    { assume "now = n"
      hence "(inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n = \<tau> n"
        unfolding inr_post_raw_def
        by (smt \<open>n < now + dly\<close> \<open>now \<le> n\<close> nat_less_le order.asym post_raw_def preempt_raw_def
        purge_raw_before_now_unchanged trans_post_raw_def)
      hence "(inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                    \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
        using assms  by (simp add: \<open>now = n\<close> zero_fun_def zero_option_def) }
    ultimately have "(inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                    \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
      by auto }
  moreover
  { assume "n = now + dly"
    hence " inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = Some val  \<or> inr_post_raw sig val (\<sigma> sig) \<tau> now dly n sig = None"
      unfolding inr_post_raw_def trans_post_raw_def post_raw_def preempt_raw_def by auto }
  ultimately show "(inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = Some val
                                    \<or>  (inr_post_raw sig val (\<sigma> sig) \<tau> now dly) n sig = None"
    by auto
qed

lemma signal_of_inr_post:
  assumes "now + dly \<le> t"
  assumes "\<forall>i < now. \<tau> i = 0"
  assumes "0 < dly"
  shows "signal_of c (inr_post_raw s v c \<tau> now dly) s t = v"
proof -
  let ?\<tau>' = "purge_raw \<tau> now dly s c v"
  have "post_necessary_raw (dly - 1) ( ?\<tau>') now s v c \<or> \<not> post_necessary_raw (dly - 1) ( ?\<tau>') now s v c"
    by auto
  moreover
  { assume "post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some (now + dly)"
    proof (rule inf_time_someI)
      show " now + dly \<in> dom (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)"
        using `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
        by (simp add: domIff inr_post_raw_def post_raw_def to_trans_raw_sig_def trans_post_raw_def)
    next
      show "now + dly \<le> t" using assms by auto
    next
      { fix ta
        assume *: "ta \<in> dom (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)"
        assume "ta \<le> t"
        have "ta \<le> now + dly"
        proof (rule ccontr)
          assume "\<not> ta \<le> now + dly"
          hence "now + dly < ta" by auto
          hence " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) ta = None"
            using \<open>0 < dly\<close> `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
            unfolding inr_post_raw_def trans_post_raw_def post_raw_def to_trans_raw_sig_def comp_def
            purge_raw_def Let_def by auto
          with * show "False" by auto
        qed }
      thus " \<forall>ta\<in>dom (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s). ta \<le> t \<longrightarrow> ta \<le> now + dly"
        by auto
    qed
    moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) (now + dly) = Some v"
      using `post_necessary_raw (dly-1) (?\<tau>') now s v c`
      unfolding inr_post_raw_def   by (simp add: post_raw_def to_trans_raw_sig_def trans_post_raw_def)
    ultimately have ?thesis
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    then obtain i where "i \<le> now + (dly-1) \<and>  (purge_raw \<tau> now dly s c v) i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s c v) j s = None) \<or>
                        (\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s c v) i s = None) \<and> v = c"
      using post_necessary_raw_correctness[of "c" "purge_raw \<tau> now dly s c v" "s" "now" "dly - 1" "v"]
      by metis
    moreover
    { assume "i \<le> now + (dly-1) \<and>  ?\<tau>' i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None)"
      hence "i \<le> now + (dly-1)" and " ?\<tau>' i s = Some v" and **: "\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None"
        by auto
      have "inf_time (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly)) s t = Some i"
      proof (rule inf_time_someI)
        show "i \<in> dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          using ` ?\<tau>' i s = Some v` not_nec `i \<le> now + (dly-1)` `0 < dly`
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
              using `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` **
              unfolding inr_post_raw_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              preempt_raw_def by auto
            with * show "False" by auto
          qed }
        thus "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> i"
          by auto
      qed
      moreover have " (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s) i = Some v"
        using `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` ` ?\<tau>' i s = Some v` `i \<le> now + (dly-1)` `0 < dly`
        unfolding inr_post_raw_def  unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def
        by auto
      ultimately have ?thesis
        unfolding to_signal_def comp_def by auto }
    moreover
    { assume "(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s c v) i s = None) \<and> v = c"
      have "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)). t < ta)"
        then obtain ta where "t \<ge> ta" and "ta\<in>dom ( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s))"
          using leI by auto
        hence "( (to_trans_raw_sig (inr_post_raw s v c \<tau> now dly) s)) ta \<noteq> 0"
          by (metis domD option.distinct(1) zero_option_def)
        moreover have "inr_post_raw s v c \<tau> now dly = trans_post_raw s v c (purge_raw \<tau> now dly s c v) now dly"
          unfolding inr_post_raw_def by auto
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
            using not_nec `(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s c v) i s = None) \<and> v = c`
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
        unfolding to_signal_def comp_def using `(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw \<tau> now dly s c v) i s = None) \<and> v = c`
        by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

lemma signal_of_inr_post':
  assumes "now + dly \<le> t"
  assumes "\<forall>i < now. \<tau> i = 0"
  assumes "0 < dly"
  shows "signal_of c (inr_post_raw' s v c \<tau> now dly) s t = v"
proof -
  let ?\<tau>' = "purge_raw' \<tau> now dly s c v"
  have "post_necessary_raw (dly - 1) ( ?\<tau>') now s v c \<or> \<not> post_necessary_raw (dly - 1) ( ?\<tau>') now s v c"
    by auto
  moreover
  { assume "post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    have "inf_time (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly)) s t = Some (now + dly)"
    proof (rule inf_time_someI)
      show " now + dly \<in> dom (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)"
        using `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
        by (simp add: domIff inr_post_raw'_def post_raw_def to_trans_raw_sig_def trans_post_raw_def)
    next
      show "now + dly \<le> t" using assms by auto
    next
      { fix ta
        assume *: "ta \<in> dom (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)"
        assume "ta \<le> t"
        have "ta \<le> now + dly"
        proof (rule ccontr)
          assume "\<not> ta \<le> now + dly"
          hence "now + dly < ta" by auto
          hence " (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s) ta = None"
            using \<open>0 < dly\<close> `post_necessary_raw (dly-1) ( ?\<tau>') now s v c`
            unfolding inr_post_raw'_def trans_post_raw_def post_raw_def to_trans_raw_sig_def comp_def
            purge_raw_def Let_def by auto
          with * show "False" by auto
        qed }
      thus " \<forall>ta\<in>dom (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s). ta \<le> t \<longrightarrow> ta \<le> now + dly"
        by auto
    qed
    moreover have " (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s) (now + dly) = Some v"
      using `post_necessary_raw (dly-1) (?\<tau>') now s v c`
      unfolding inr_post_raw'_def   by (simp add: post_raw_def to_trans_raw_sig_def trans_post_raw_def)
    ultimately have ?thesis
      unfolding to_signal_def comp_def by auto }
  moreover
  { assume not_nec: "\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c"
    then obtain i where "i \<le> now + (dly-1) \<and>  (purge_raw' \<tau> now dly s c v) i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  (purge_raw' \<tau> now dly s c v) j s = None) \<or>
                        (\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw' \<tau> now dly s c v) i s = None) \<and> v = c"
      using post_necessary_raw_correctness[of "c" "purge_raw' \<tau> now dly s c v" "s" "now" "dly - 1" "v"]
      by metis
    moreover
    { assume "i \<le> now + (dly-1) \<and>  ?\<tau>' i s = Some v \<and> (\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None)"
      hence "i \<le> now + (dly-1)" and " ?\<tau>' i s = Some v" and **: "\<forall>j>i. j \<le> now + (dly-1) \<longrightarrow>  ?\<tau>' j s = None"
        by auto
      have "inf_time (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly)) s t = Some i"
      proof (rule inf_time_someI)
        show "i \<in> dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s))"
          using ` ?\<tau>' i s = Some v` not_nec `i \<le> now + (dly-1)` `0 < dly`
          unfolding inr_post_raw'_def  unfolding trans_post_raw_def to_trans_raw_sig_def preempt_raw_def
          by auto
      next
        show "i \<le> t"
          using `i  \<le> now + (dly-1)` assms by auto
      next
        { fix ta
          assume *: "ta \<in> dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s))"
          assume "ta \<le> t"
          have "ta \<le> i"
          proof (rule ccontr)
            assume "\<not> ta \<le> i"
            hence "i < ta" by auto
            hence " (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s) ta = None"
              using `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` **
              unfolding inr_post_raw'_def  unfolding trans_post_raw_def to_trans_raw_sig_def
              preempt_raw_def by auto
            with * show "False" by auto
          qed }
        thus "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> i"
          by auto
      qed
      moreover have " (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s) i = Some v"
        using `\<not> post_necessary_raw (dly-1) ( ?\<tau>') now s v c` ` ?\<tau>' i s = Some v` `i \<le> now + (dly-1)` `0 < dly`
        unfolding inr_post_raw'_def  unfolding to_trans_raw_sig_def trans_post_raw_def preempt_raw_def
        by auto
      ultimately have ?thesis
        unfolding to_signal_def comp_def by auto }
    moreover
    { assume "(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw' \<tau> now dly s c v) i s = None) \<and> v = c"
      have "\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)). t < ta"
      proof (rule ccontr)
        assume "\<not> (\<forall>ta\<in>dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)). t < ta)"
        then obtain ta where "t \<ge> ta" and "ta\<in>dom ( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s))"
          using leI by auto
        hence "( (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly) s)) ta \<noteq> 0"
          by (metis domD option.distinct(1) zero_option_def)
        moreover have "inr_post_raw' s v c \<tau> now dly = trans_post_raw s v c (purge_raw' \<tau> now dly s c v) now dly"
          unfolding inr_post_raw'_def by auto
        ultimately have absurd: " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta \<noteq> 0"
          by auto
        have "ta < now \<or> now \<le> ta \<and> ta \<le> now + dly \<or> now + dly < ta"
          by auto
        moreover
        { assume "ta < now"
          hence " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta = 0"
            using assms(2) not_nec purge_raw'_before_now_unchanged[of "\<tau>" "now" "dly" "s"]
            unfolding to_trans_raw_sig_def preempt_raw_def
            by (metis add_le_same_cancel1 assms(3) leI le_less_trans nat_less_le to_trans_raw_sig_def
            trans_post_less zero_fun_def)
          with absurd have False by auto }
        moreover
        { assume "now \<le> ta \<and> ta \<le> now + dly"
          hence " (to_trans_raw_sig (trans_post_raw s v c ?\<tau>' now dly) s) ta = 0"
            using not_nec `(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw' \<tau> now dly s c v) i s = None) \<and> v = c`
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
      hence "inf_time (to_trans_raw_sig (inr_post_raw' s v c \<tau> now dly)) s t = None"
        by (auto simp add: inf_time_none_iff)
      hence ?thesis
        unfolding to_signal_def comp_def using `(\<forall>i. i \<le> now + (dly-1) \<longrightarrow>  (purge_raw' \<tau> now dly s c v) i s = None) \<and> v = c`
        by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed


inductive b_seq_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal history \<Rightarrow> 'signal state \<Rightarrow>
                                         'signal seq_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  ("_ , _ , _ , _, _  \<turnstile> <_ , _> \<longrightarrow>\<^sub>s _") where
  "b_seq_exec t \<sigma> \<gamma> \<theta> def  Bnull \<tau> \<tau>"

| "b_seq_exec t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' \<Longrightarrow> b_seq_exec t \<sigma> \<gamma> \<theta> def ss2 \<tau>'' \<tau>' \<Longrightarrow>
                                                        b_seq_exec t \<sigma> \<gamma> \<theta>  def (Bcomp ss1 ss2) \<tau> \<tau>'"

| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> guard \<longrightarrow>\<^sub>b (Bv True)  \<Longrightarrow> b_seq_exec t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>' \<Longrightarrow>
                                               b_seq_exec t \<sigma> \<gamma> \<theta> def (Bguarded guard ss1 ss2) \<tau> \<tau>'"

| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> guard \<longrightarrow>\<^sub>b (Bv False) \<Longrightarrow> b_seq_exec t \<sigma> \<gamma> \<theta> def  ss2 \<tau> \<tau>' \<Longrightarrow>
                                               b_seq_exec t \<sigma> \<gamma> \<theta> def (Bguarded guard ss1 ss2) \<tau> \<tau>'"

| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> e \<longrightarrow>\<^sub>b x \<Longrightarrow> trans_post_raw sig x (\<sigma> sig) \<tau> t dly = \<tau>' \<Longrightarrow>
                                              b_seq_exec t \<sigma> \<gamma> \<theta>  def (Bassign_trans sig e dly) \<tau> \<tau>'"

| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> e \<longrightarrow>\<^sub>b x \<Longrightarrow> inr_post_raw' sig x (\<sigma> sig) \<tau> t dly = \<tau>' \<Longrightarrow>
                                              b_seq_exec t \<sigma> \<gamma> \<theta>  def (Bassign_inert sig e dly) \<tau> \<tau>'"

\<comment> \<open>case matches current choice\<close>
| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x \<Longrightarrow> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x \<Longrightarrow>
   b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow>
   b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"

\<comment> \<open>case does not match current choice\<close>
| "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp \<longrightarrow>\<^sub>b x \<Longrightarrow> t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x' \<Longrightarrow> x \<noteq> x' \<Longrightarrow>
   b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp choices) \<tau> \<tau>' \<Longrightarrow>
   b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Explicit exp', ss) # choices)) \<tau> \<tau>'"

\<comment> \<open>case others\<close>
| "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow>
   b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp ((Others, ss) # choices)) \<tau> \<tau>'"

\<comment> \<open>case does not match any choices\<close>
| "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bcase exp []) \<tau> \<tau>"

inductive_cases seq_cases [elim!]: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bnull, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and
  seq_cases_bcomp: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and
  seq_cases_bguarded: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bguarded guard ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and
  seq_cases_trans: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_trans sig e dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and
  seq_cases_inert: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bassign_inert sig e dly, \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and
  seq_cases_bcase: "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcase exp choices, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"

lemma b_seq_exec_deterministic_weaker:
  assumes   "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>1"
  assumes   "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>2"
  assumes   "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows "\<tau>2 = \<tau>1"
  using assms
proof (induction arbitrary:\<tau>2 \<theta>2 rule:b_seq_exec.induct)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case  using beval_raw_deterministic by blast+
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  then show ?case by (metis (full_types) seq_cases_bcomp)
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case
    by (metis beval_raw_deterministic_weaker seq_cases_bguarded val.sel(1))
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case
    by (metis beval_raw_deterministic_weaker seq_cases_bguarded val.sel(1))
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case
    by (metis beval_raw_deterministic_weaker seq_cases_trans)
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case using beval_raw_deterministic_weaker
    by (metis seq_cases_inert)
next
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  show ?case
    apply (rule seq_cases_bcase[OF 7(5), rotated])
       apply (metis "7.hyps"(1) "7.hyps"(2) "7.prems"(2) beval_raw_deterministic_weaker choices.sel list.sel(1) prod.sel(1))
    using "7.IH" "7.prems"(2) by auto
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
  show ?case
    apply (rule seq_cases_bcase[OF 8(6)])
       apply (metis "8.hyps"(1) "8.hyps"(2) "8.hyps"(3) "8.prems"(2) Pair_inject beval_raw_deterministic_weaker choices.inject list.inject)
    using "8.IH" "8.prems"(2) by auto
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
  show ?case
    apply (rule seq_cases_bcase[OF 9(3)])
    using "9.IH" "9.prems"(2) by auto
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case using seq_cases_bcase  by blast
qed

lemma b_seq_exec_deterministic:
  assumes   "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>1"
  assumes   "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>2"
  shows "\<tau>2 = \<tau>1"
  using assms b_seq_exec_deterministic_weaker by fastforce

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> <Bnull, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  shows "\<tau>' = \<tau>"
  using assms by auto

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>_temp"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss2, \<tau>_temp> \<longrightarrow>\<^sub>s \<tau>_final"
  shows "\<tau>' = \<tau>_final"
  using assms by (meson b_seq_exec.intros(2) b_seq_exec_deterministic)

lemma b_seq_exec_almost_all_zero:
  fixes \<tau> :: "'signal trans_raw"
  fixes \<theta> :: "'signal history"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  assumes "\<forall>\<^sub>\<infinity>x. app_time \<theta> x = 0"
  assumes "\<forall>\<^sub>\<infinity>x. \<tau> x = 0"
  shows "\<forall>\<^sub>\<infinity>x. \<tau>' x = 0"
  using assms
  by (induction rule:b_seq_exec.induct)
      (auto simp add: trans_post_raw_almost_all_zero inr_post_raw_almost_all_zero')
                                                                  
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
  "\<And>n. dom (map_diff_trans_raw (purge_raw \<tau> t dly sig def val) \<tau> n) \<subseteq> {sig}"
  by (smt domIff insertCI map_diff_def purge_raw_does_not_affect_other_sig subsetI)

lemma dom_map_diff_purge':
  "\<And>n. dom (map_diff_trans_raw (purge_raw' \<tau> t dly sig def val) \<tau> n) \<subseteq> {sig}"
  by (smt domIff insertCI map_diff_def purge_raw_does_not_affect_other_sig' subsetI)

lemma dom_map_diff_inr_post:
  fixes sig x cur_val \<tau> t dly n
  defines "\<tau>' \<equiv> inr_post_raw sig x cur_val \<tau> t dly"
  shows "dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> {sig}"
  by (metis Un_empty_right assms dom_map_diff_purge dom_map_diff_subseteq dom_map_diff_trans_post
  inr_post_raw_def subset_Un_eq subset_singleton_iff)

lemma dom_map_diff_inr_post':
  fixes sig x cur_val \<tau> t dly n
  defines "\<tau>' \<equiv> inr_post_raw' sig x cur_val \<tau> t dly"
  shows "dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> {sig}"
  by (smt assms domIff inr_post_raw_does_not_affect_other_sig' insertCI map_diff_def subsetI)

lemma seq_stmts_modify_local_only_raw:
  assumes "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
  shows "\<And>n. dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> set (signals_in ss)"
  using assms
proof (induction rule:b_seq_exec.inducts)
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  have " signals_of (Bcase exp ((Explicit exp', ss) # choices)) = signals_of ss \<union> signals_of (Bcase exp choices)"
    by auto
  also have "... \<supseteq> signals_of ss"
    by auto
  then show ?case
    using "7.IH" calculation by blast
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau> \<tau>' ss)
  have "signals_of (Bcase exp ((Explicit exp', ss) # choices)) = signals_of ss \<union> signals_of (Bcase exp choices)"
    by auto
  hence "... \<supseteq> signals_of (Bcase exp choices)"
    by auto
  then show ?case
    using "8.IH" \<open>signals_of (Bcase exp ((Explicit exp', ss) # choices)) = signals_of ss \<union>
    signals_of (Bcase exp choices)\<close> by blast
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp choices)
  have "signals_of (Bcase exp ((Others, ss) # choices)) = signals_of ss \<union> signals_of (Bcase exp choices)"
    by auto
  hence "signals_of ss \<subseteq> signals_of (Bcase exp ((Others, ss) # choices))"
    by auto
  then show ?case
    using "9.IH" by blast
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case by simp
next
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcomp ss1 ss2, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (meson b_seq_exec.intros(2))
  have "dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> dom (map_diff (\<tau>' n) (\<tau>'' n)) \<union> dom (map_diff (\<tau>'' n) (\<tau> n))"
    using dom_map_diff_subseteq by metis
  also have "... \<subseteq> signals_of ss2 \<union> dom (map_diff ( \<tau>'' n) ( \<tau> n))"
    using 2(4)[of "n"]  by(auto intro: Un_mono)
  also have "... \<subseteq> signals_of ss2 \<union> signals_of ss1"
    using 2(3)[of "n"] by (auto intro:Un_mono)
  finally show ?case
    by auto
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case by auto
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case by auto
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case
    using dom_map_diff_trans_post by force
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  then show ?case using dom_map_diff_inr_post' by force 
qed

text \<open>An important theorem: the semantics of sequential statements only modifies local variables.\<close>

theorem seq_stmts_modify_local_only:
  assumes "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
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

lemma trans_post_preserve_trans_removal_nonstrict:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "0 < dly"
  shows "\<And>n. n \<le> t \<Longrightarrow> (trans_post_raw sig x def \<tau> t dly) n = 0"
  using assms  by (auto simp add: preempt_raw_def trans_post_raw_def post_raw_def)

lemma purge_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (purge_raw \<tau> t dly sig def val) n = 0"
  using assms
  by (metis less_or_eq_imp_le purge_raw_before_now_unchanged)

lemma purge_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (purge_raw' \<tau> t dly sig def val) n = 0"
  using assms
  by (metis less_or_eq_imp_le purge_raw_before_now_unchanged')

lemma purge_preserve_trans_removal_nonstrict:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n \<le> t \<Longrightarrow> (purge_raw \<tau> t dly sig def val) n = 0"
  using assms  by (metis purge_raw_before_now_unchanged)

lemma purge_preserve_trans_removal_nonstrict':
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n \<le> t \<Longrightarrow> (purge_raw' \<tau> t dly sig def val) n = 0"
  using assms  by (metis purge_raw_before_now_unchanged')

lemma inr_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (inr_post_raw sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal)

lemma inr_post_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (inr_post_raw' sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw'_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal')

lemma inr_post_preserve_trans_removal_nonstrict:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "0 < dly"
  shows "\<And>n. n \<le> t \<Longrightarrow> (inr_post_raw sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw_def
  by (auto simp add: trans_post_preserve_trans_removal_nonstrict purge_preserve_trans_removal_nonstrict)

lemma inr_post_preserve_trans_removal_nonstrict':
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "0 < dly"
  shows "\<And>n. n \<le> t \<Longrightarrow> (inr_post_raw' sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_raw'_def
  by (auto simp add: trans_post_preserve_trans_removal_nonstrict purge_preserve_trans_removal_nonstrict')

lemma switch_signal_ex_mapping:
  assumes "signal_of (\<sigma> s) \<tau> s now \<noteq> v" and "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n s = 0"
  shows "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v"
proof (rule ccontr)
  assume "\<not> (\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v)"
  hence 0: "\<forall>n. now < n \<and> n \<le> now + dly \<longrightarrow> \<tau> n s = None \<or> \<tau> n s \<noteq> Some (v)"
    by fastforce
  hence "signal_of (\<sigma> s) \<tau> s (now + dly) \<noteq> v"
  proof (cases "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = None")
    case True
    have "inf_time (to_trans_raw_sig \<tau>) s now = None"
      unfolding sym[OF inf_time_none_iff] using assms
      by (metis True domIff dual_order.trans inf_time_noneE2 le_add1 not_le_imp_less zero_option_def)
    hence "\<sigma> s \<noteq> v"
      using assms(1)
      unfolding to_signal_def comp_def by auto
    then show ?thesis
      unfolding to_signal_def comp_def using True by auto
  next
    case False
    then obtain time where inf: "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some time"
      by auto
    hence "time \<in> keys (to_trans_raw_sig \<tau> s) \<and> time \<le> now + dly"
      using inf_time_some_exists by fastforce
    hence "\<tau> time s \<noteq> None" and "time \<le> now + dly"
      unfolding keys_def to_trans_raw_sig_def  by (simp add: zero_option_def)+
    hence "now < time"
      using assms(3)  by (metis leI zero_fun_def zero_option_def)
    with \<open>time \<le> now + dly\<close> have "\<tau> time s \<noteq> Some v"
      using 0 \<open>\<tau> time s \<noteq> None\<close> by auto
    then show ?thesis
      unfolding to_signal_def comp_def using inf
      by (metis \<open>\<tau> time s \<noteq> None\<close> option.exhaust_sel option.simps(5) to_trans_raw_sig_def)
  qed
  with assms(2) show False
    by auto
qed

lemma switch_signal_ex_mapping_gen:
  assumes "signal_of def \<tau> s now \<noteq> v" and "signal_of def \<tau> s (now + dly) = v"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n s = 0"
  shows "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v"
  using switch_signal_ex_mapping assms 
  by (simp add: switch_signal_ex_mapping)

lemma earlier_post_time:
  assumes "signal_of (\<sigma> s) \<tau> s now \<noteq> v" and "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  shows "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
proof -
  let ?time = "GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) s (now + dly)"
  have *: "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v"
    using switch_signal_ex_mapping[of "\<sigma>", OF `signal_of (\<sigma> s) \<tau> s now \<noteq> v` `signal_of (\<sigma> s) \<tau> s (now + dly) = v`] assms(3)
    by (simp add: zero_fun_def)
  hence "?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly"
    using GreatestI_ex_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some v" and b="now + dly"]
    unfolding keys_def to_trans_raw_sig_def
    by (metis (mono_tags, lifting) CollectI option.simps(3) zero_option_def)
  have "\<tau> ?time s = Some v"
    by (smt "*" GreatestI_nat)
  have assms4: "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
    using assms(2) by auto
  have **: "\<exists>m\<le>now + dly. to_trans_raw_sig \<tau> s m = Some v \<and> (\<forall>j>m. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None)"
    using signal_of_elim[OF assms4] *  by auto
  have "\<forall>j > ?time. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None"
  proof (rule ccontr)
    assume "\<not> (\<forall>j > ?time. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None)"
    then obtain j where "j > ?time" and "j \<le> now + dly" and "to_trans_raw_sig \<tau> s j \<noteq> None"
      by blast
    hence "to_trans_raw_sig \<tau> s j \<noteq> Some v"
      using Greatest_le_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some v" and b="now + dly"]
    proof -
      obtain nn :: nat and nna :: nat where
        f1: "\<And>n na. nn \<le> now + dly \<and> nna \<le> now + dly \<and> to_trans_raw_sig \<tau> s nna = Some v \<and> (\<not> nna < n \<or> \<not> n \<le> now + dly \<or> to_trans_raw_sig \<tau> s n = None) \<and> (\<not> nn \<le> now + dly \<or> \<not> na \<le> now + dly \<or> \<tau> na s \<noteq> Some v \<or> na \<le> (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v))"
        using "**" \<open>\<And>k. \<lbrakk>k \<le> now + dly \<and> \<tau> k s = Some v; \<forall>y. y \<le> now + dly \<and> \<tau> y s = Some v \<longrightarrow> y \<le> now + dly\<rbrakk> \<Longrightarrow> k \<le> (GREATEST x. x \<le> now + dly \<and> \<tau> x s = Some v)\<close> by auto
      then have "\<tau> nna s = Some v"
        by (simp add: to_trans_raw_sig_def)
      then have False
        using f1 \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) < j\<close> \<open>j \<le> now + dly\<close> \<open>to_trans_raw_sig \<tau> s j \<noteq> None\<close> by fastforce
      then show ?thesis
        by meson
    qed
    have "\<forall>m \<le> now + dly. to_trans_raw_sig \<tau> s m = Some v \<longrightarrow> \<not> (\<forall>j > m. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None)"
    proof (rule, rule, rule)
      fix m
      assume "m \<le> now + dly"
      assume "to_trans_raw_sig \<tau> s m = Some v"
      hence "\<tau> m s = Some v"
        by (simp add: to_trans_raw_sig_def)
      hence "m \<le> ?time"
        using Greatest_le_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some v" and b="now + dly"]
        \<open>m \<le> now + dly\<close> by auto
      have "j > m \<and> j \<le> now + dly \<and> to_trans_raw_sig \<tau> s j \<noteq> None"
        using \<open>j > ?time\<close> \<open>?time \<ge> m\<close> \<open>j \<le> now + dly\<close> \<open>to_trans_raw_sig \<tau> s j \<noteq> Some v\<close>
        le_less_trans \<open>to_trans_raw_sig \<tau> s j \<noteq> None\<close> by blast
      thus " \<not> (\<forall>j>m. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None)"
        by auto
    qed
    with ** show False
      by auto
  qed
  hence "\<forall>t\<in>dom (to_trans_raw_sig \<tau> s). t \<le> now + dly \<longrightarrow> t \<le> ?time"
    by (meson domIff not_le_imp_less)
  show "?k2 = Some ?time"
  proof (intro inf_time_someI)
    show "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<in> dom (to_trans_raw_sig \<tau> s)"
      by (metis (full_types) \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<in> keys (to_trans_raw_sig
      \<tau> s) \<and> (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> now + dly\<close> dom_def keys_def
      zero_option_def)
  next
    show "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> now + dly"
      using \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<in> keys (to_trans_raw_sig \<tau> s) \<and> (GREATEST
      n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> now + dly\<close> by blast
  next
    show " \<forall>t\<in>dom (to_trans_raw_sig \<tau> s). t \<le> now + dly \<longrightarrow> t \<le> (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
      using \<open>\<forall>t\<in>dom (to_trans_raw_sig \<tau> s). t \<le> now + dly \<longrightarrow> t \<le> (GREATEST n. n \<le> now + dly \<and> \<tau> n s =
      Some v)\<close> by blast
  qed
qed

lemma earlier_post_time_general:
  assumes "signal_of def \<tau> s now \<noteq> v" and "signal_of def \<tau> s (now + dly) = v"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  shows "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
  using earlier_post_time[where s="s" and \<sigma>="(\<lambda>x. _)(s := def)"] assms by auto
  
lemma signal_of_inr_post2:
  assumes "now \<le> t"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  assumes "\<sigma> s \<noteq> v" and "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
  assumes "t < (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
  shows "signal_of (\<sigma> s) (inr_post_raw s v (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)"
  using assms
proof (cases "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = None")
  case True
  then show ?thesis  unfolding to_signal_def comp_def by auto
next
  let ?time = "GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) s (now + dly)"
  have 0: "signal_of (\<sigma> s) \<tau> s now \<noteq> v"
    using assms(2-3)  by (metis signal_of_val_eq zero_fun_def zero_option_def)
  have 1: "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
    using assms(4)  by auto
  have "?k2 = Some ?time"
    using earlier_post_time[of "\<sigma>", OF 0 1 assms(2)] by auto
  have "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v"
    using switch_signal_ex_mapping[of "\<sigma>", OF 0 1] assms(2)
    by (simp add: zero_fun_def)
  hence "?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly"
    using GreatestI_ex_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some v" and b="now + dly"]
    unfolding keys_def to_trans_raw_sig_def
    by (metis (mono_tags, lifting) CollectI option.simps(3) zero_option_def)
  case False
  then obtain t' where inf: "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = Some t'"
    by auto
  hence "t' \<le> t"
    using assms(2) by (auto dest!: inf_time_at_most)
  hence "purge_raw \<tau> now dly s (\<sigma> s) v = override_on \<tau> (\<lambda>n. (\<tau> n)(s := None)) ({now<..<the ?k2} \<union> {the ?k2<..now + dly})"
    using assms(3-4) unfolding purge_raw_def Let_def
    by (metis (mono_tags, hide_lams) assms(2) option.distinct(1) signal_of_elim to_trans_raw_sig_def
    zero_fun_def zero_option_def)
  also have "... = override_on \<tau> (\<lambda>n. (\<tau> n)(s := None)) ({now<..<?time} \<union> {?time<..now + dly})"
    using `?k2 = Some ?time` by auto
  finally have purge_raw_alt_def: "purge_raw \<tau> now dly s (\<sigma> s) v = override_on \<tau> (\<lambda>n. (\<tau> n)(s := None)) ({now<..<?time} \<union> {?time<..now + dly})"
    by auto
  have *: "\<And>n. n < now \<Longrightarrow>  \<tau> n = 0"
    using assms(2) by auto
  have **: "\<And>n. n < now \<Longrightarrow>  (inr_post_raw s v (\<sigma> s) \<tau> now dly) n = 0"
    by (simp add: "*" inr_post_preserve_trans_removal)
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
  have asm4: "\<tau> now = 0"
    using assms(2) by (auto simp add: zero_fun_def zero_option_def)
  have "t' < ?time"
    using \<open>t' \<le> t\<close> assms(5) le_less_trans by blast
  have "inr_post_raw s v (\<sigma> s) \<tau> now dly t' s = trans_post_raw s v (\<sigma> s) (purge_raw \<tau> now dly s (\<sigma> s) v) now dly t' s"
    unfolding inr_post_raw_def by auto
  also have "...  = purge_raw \<tau> now dly s (\<sigma> s) v t' s"
    using `now \<le> t'` `t' < ?time` `?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly`
    unfolding trans_post_raw_def post_raw_def preempt_raw_def by auto
  also have "... = None"
    unfolding purge_raw_alt_def using `now \<le> t'` `\<tau> now = 0` `t' < ?time`
    by (metis (mono_tags, lifting) Un_iff fun_upd_same greaterThanLessThan_iff le_neq_implies_less
    override_on_apply_in purge_raw_alt_def purge_raw_before_now_unchanged zero_fun_def
    zero_option_def)
  finally have "inr_post_raw s v (\<sigma> s) \<tau> now dly t' s = None"
    by auto
  moreover have "t' \<in> dom ( (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s))"
    using inf_time_some_exists[OF inf] unfolding dom_is_keys by auto
  ultimately have False
    by (metis (full_types) domD option.distinct(1) to_trans_raw_sig_def)
  thus ?thesis
    by auto
qed

lemma signal_of_inr_post2'_bv:
  assumes "now \<le> t"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  assumes "\<sigma> s \<noteq> (Bv b)" and "signal_of (\<sigma> s) \<tau> s (now + dly) = (Bv b)"
  assumes "t < (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some (Bv b))"
  shows "signal_of (\<sigma> s) (inr_post_raw' s (Bv b) (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)"
  using signal_of_inr_post2[OF assms(1-2)] unfolding inr_post_raw'_def inr_post_raw_def purge_raw'_def 
  using assms(3) assms(4) assms(5) by fastforce

lemma to_bit_signal_of':
  assumes "to_bit b (signal_of def \<tau> sig t) = v"
  shows   "signal_of (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b \<Rightarrow> b)) (to_trans_raw_bit def \<tau> b sig) sig t = v"
  using assms
proof (cases "inf_time (to_trans_raw_sig \<tau>) sig t")
  case None
  hence "signal_of def \<tau> sig t = def"
    unfolding to_signal_def comp_def by auto
  hence "to_bit b (def) = v"
    using assms by auto
  have "inf_time (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig)) sig t = None"
    unfolding inf_time_none_iff[THEN sym]
  proof 
    fix x
    assume " x \<in> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)"
    hence "to_trans_raw_bit def \<tau> b sig x sig \<noteq> None"
      unfolding to_trans_raw_sig_def dom_def by auto
    hence "\<tau> x sig \<noteq> None"
      unfolding to_trans_raw_bit_def  using option.simps(4) by fastforce
    thus "t < x"
      using None unfolding inf_time_none_iff[THEN sym]  by (simp add: domIff to_trans_raw_sig_def)
  qed
  hence "signal_of (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b \<Rightarrow> b)) (to_trans_raw_bit def \<tau> b sig) sig t = (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b \<Rightarrow> b))"
    unfolding to_signal_def comp_def by auto
  also have "... = v"
    using `to_bit b (def) = v`  by (auto split: val.splits)
  finally show ?thesis 
    by auto
next
  case (Some a)
  hence "signal_of (def) \<tau> sig t = the (to_trans_raw_sig \<tau> sig a)"
    unfolding to_signal_def comp_def by auto
  hence "to_bit b (the (to_trans_raw_sig \<tau> sig a)) = v"
    using assms by auto
  have " inf_time (to_trans_raw_sig \<tau>) sig a = Some a"
    using Some 
    by (metis (mono_tags) dom_def dual_order.asym inf_time_neq_t_choice inf_time_some_exists keys_def nat_less_le order_refl zero_option_def)
  hence "signal_of def \<tau> sig t = signal_of def \<tau> sig a"
    using Some unfolding comp_def to_signal_def by auto
  hence "to_bit b (signal_of def \<tau> sig a) = v "
    using assms by auto
  moreover have "a \<le> t"
    using Some  by (meson inf_time_at_most)
  moreover have " \<forall>ta\<in>dom (to_trans_raw_sig \<tau> sig). ta \<le> t \<longrightarrow> ta \<le> a"
    using inf_time_someE[OF Some] by auto
  ultimately show ?thesis
  proof (induction a arbitrary: v t)
    case 0
    have "\<tau> 0 sig \<noteq> None \<or> \<tau> 0 sig = None"
      by auto
    moreover
    { assume "\<tau> 0 sig \<noteq> None"
      have "to_bit b def = to_bit b (the (\<tau> 0 sig)) \<or> to_bit b def \<noteq> to_bit b (the (\<tau> 0 sig))"
        by auto
      moreover
      { assume "to_bit b def \<noteq> to_bit b (the (\<tau> 0 sig))"
        hence "to_trans_raw_bit def \<tau> b sig 0 sig = Some (to_bit b (the (\<tau> 0 sig)))"
          using \<open>\<tau> 0 sig \<noteq> None\<close>  unfolding to_trans_raw_bit_def to_trans_raw_sig_def by auto
        moreover have "\<forall>ta\<in>dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig). ta \<le> t \<longrightarrow> ta \<le> 0"
          using 0(3) 
        proof -
          { fix nn :: nat
            have "\<tau> nn sig = None \<longrightarrow> to_trans_raw_bit def \<tau> b sig nn sig = None"
              by (simp add: to_trans_raw_bit_def)
            then have "nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig) \<or> \<not> nn \<le> t \<or> nn \<le> 0"
              by (metis (no_types) "0.prems"(3) domIff to_trans_raw_sig_def) }
          then show ?thesis
            by blast
        qed
        ultimately have " inf_time (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig)) sig t = Some 0"
          by (intro inf_time_someI)(auto simp add: dom_def to_trans_raw_sig_def)
        hence ?case
          using \<open>to_trans_raw_bit def \<tau> b sig 0 sig = Some (to_bit b (the (\<tau> 0 sig)))\<close> 0(1)
          unfolding to_trans_raw_sig_def to_signal_def comp_def 
          using \<open>\<tau> 0 sig \<noteq> None\<close> inf_time_someI by force }
      moreover
      { assume "to_bit b def = to_bit b (the (\<tau> 0 sig))"
        hence "to_bit b def = v"
          using 0(1) unfolding to_trans_raw_sig_def 
          by (smt \<open>\<tau> 0 sig \<noteq> None\<close> comp_apply domIff inf_time_someI option.case_eq_if option.sel to_signal_def zero_le)
        have "to_trans_raw_bit def \<tau> b sig 0 sig = None"
          using \<open>to_bit b def = to_bit b (the (\<tau> 0 sig))\<close> \<open>\<tau> 0 sig \<noteq> None\<close>  unfolding to_trans_raw_bit_def to_trans_raw_sig_def   
          by auto
        hence "inf_time (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig)) sig t = None"
          unfolding inf_time_none_iff[THEN sym]
          using 0 
          proof -
          { fix nn :: nat
          { assume "nn \<noteq> 0"
          moreover
          { assume "nn \<le> t \<and> \<not> nn \<le> 0"
            then have "\<tau> nn sig = None"
              by (metis \<open>\<forall>ta\<in>dom (to_trans_raw_sig \<tau> sig). ta \<le> t \<longrightarrow> ta \<le> 0\<close> domIff to_trans_raw_sig_def)
            then have "to_trans_raw_bit def \<tau> b sig nn sig = None"
              by (simp add: to_trans_raw_bit_def) }
            ultimately have "(t < nn \<or> nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)) \<or> to_trans_raw_bit def \<tau> b sig nn sig = None"
              by (meson leI le_zero_eq) }
            then have "t < nn \<or> nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)"
              by (metis (no_types) \<open>to_trans_raw_bit def \<tau> b sig 0 sig = None\<close> domIff to_trans_raw_sig_def) }
          then show "Ball (dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)) ((<) t)"
          by auto
          qed
        hence "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))"
          unfolding to_signal_def comp_def by auto
        also have "... = v"
          using \<open>to_bit b def = v\<close> using to_bit.simps by (auto split:val.splits)
        finally have ?case
          by auto }
      ultimately have ?case
        by auto }
    moreover
    { assume "\<tau> 0 sig = None"
      hence "to_bit b def = v"
        by (metis "0.prems"(1) signal_of_zero zero_option_def)
      have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = 
            signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig 0"
      proof (rule signal_of_less_ind')
        fix n 
        assume "0 < n" and "n \<le> t"
        thus "to_trans_raw_bit def \<tau> b sig n sig = 0"
        proof -
          have "\<tau> n sig = None"
            by (metis (no_types) "0.prems"(3) \<open>0 < n\<close> \<open>n \<le> t\<close> domIff leD to_trans_raw_sig_def)
          then show ?thesis
            by (simp add: to_trans_raw_bit_def zero_option_def)
        qed
      qed (auto)
      also have "... = (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b))"
        using `\<tau> 0 sig = None`  by (smt le_zero_eq option.simps(4) signal_of_def to_trans_raw_bit_def zero_option_def)
      also have "... = v"
        using `to_bit b def = v`  by (smt leD le_boolD to_bit.simps(1) to_bit.simps(2) val.split_sels(2))
      finally have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = v"
        by auto 
      hence ?case
        using 0 by auto }
    ultimately show ?case 
      by auto
  next
    case (Suc a')
    have "\<tau> (Suc a') sig = None \<or> \<tau> (Suc a') sig \<noteq> None"
      by auto
    moreover
    {  assume "\<tau> (Suc a') sig \<noteq> None"
      have "to_bit b (signal_of def \<tau> sig (Suc a' - 1)) = to_bit b (the (\<tau> (Suc a') sig)) \<or> to_bit b (signal_of def \<tau> sig (Suc a' - 1)) \<noteq> to_bit b (the (\<tau> (Suc a') sig))"
        by auto
      moreover
      { have *: "\<forall>ta\<in>dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig). ta \<le> t \<longrightarrow> ta \<le> Suc a'"
          using Suc 
        proof -
          { fix nn :: nat
            { assume "\<tau> nn sig \<noteq> None"
              then have "\<not> nn \<le> t \<or> nn \<le> Suc a' \<or> nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)"
                by (simp add: Suc.prems(3) domIff to_trans_raw_sig_def) }
            moreover
            { assume "(case \<tau> nn sig of None \<Rightarrow> None | Some v \<Rightarrow> if 0 < nn \<and> to_bit b (signal_of def \<tau> sig (nn - 1)) = to_bit b v then None else if nn = 0 \<and> to_bit b def = to_bit b v then None else Some (to_bit b v)) = None"
              then have "\<not> nn \<le> t \<or> nn \<le> Suc a' \<or> nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)"
                by (simp add: domIff to_trans_raw_bit_def to_trans_raw_sig_def) }
            ultimately have "\<not> nn \<le> t \<or> nn \<le> Suc a' \<or> nn \<notin> dom (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig) sig)"
              by force }
          then show ?thesis
            by meson
        qed
        assume "to_bit b (signal_of def \<tau> sig (Suc a' - 1)) \<noteq> to_bit b (the (\<tau> (Suc a') sig))"
        hence "(to_trans_raw_bit def \<tau> b sig) (Suc a') sig = Some (to_bit b (the (\<tau> (Suc a') sig)))"
          unfolding to_trans_raw_bit_def using \<open>\<tau> (Suc a') sig \<noteq> None\<close> by auto
        also have "... = Some v"
          using Suc unfolding to_trans_raw_sig_def comp_def 
          by (smt calculation domIff inf_time_someI option.case_eq_if option.sel option.simps(3) to_signal_def to_trans_raw_bit_def)
        finally have "inf_time (to_trans_raw_sig (to_trans_raw_bit def \<tau> b sig)) sig t = Some (Suc a')"
          by (intro inf_time_someI)(auto simp add: dom_def to_trans_raw_sig_def * `Suc a' \<le> t`)
        hence ?case
          using Suc unfolding to_signal_def comp_def 
          by (simp add: \<open>Some (to_bit b (the (\<tau> (Suc a') sig))) = Some v\<close> \<open>to_trans_raw_bit def \<tau> b sig (Suc a') sig = Some (to_bit b (the (\<tau> (Suc a') sig)))\<close> to_trans_raw_sig_def) }
      moreover
      { assume "to_bit b (signal_of def \<tau> sig (Suc a' - 1)) = to_bit b (the (\<tau> (Suc a') sig))"
        hence *: "to_bit b (signal_of def \<tau> sig a') = to_bit b (the (\<tau> (Suc a') sig))"
          by auto
        also have "... = v"
        proof -
          have "inf_time (to_trans_raw_sig \<tau>) sig (Suc a') = Some (Suc a')"
            by (meson \<open>\<tau> (Suc a') sig \<noteq> None\<close> option.exhaust_sel some_inf_time')
          hence "signal_of def \<tau> sig (Suc a') = the ((\<tau> (Suc a') sig))"
            unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
          thus ?thesis
            using Suc(2) by auto
        qed
        finally have "(to_trans_raw_bit def \<tau> b sig) (Suc a') sig = None"
          unfolding to_trans_raw_bit_def 
          by (smt \<open>to_bit b (signal_of def \<tau> sig (Suc a' - 1)) = to_bit b (the (\<tau> (Suc a') sig))\<close>
          option.case_eq_if zero_less_Suc)
        have "a' \<le> t"
          using `Suc a' \<le> t` by auto
        have h0: "to_bit b (signal_of def \<tau> sig a') = v"
          using "*" \<open>to_bit b (the (\<tau> (Suc a') sig)) = v\<close> by blast        
        have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig a' = v"
          using Suc(1)[OF h0 order.refl] by auto
        moreover have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = 
                       signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig (Suc a')"
        proof (rule signal_of_less_ind')    
          fix n
          assume "Suc a' < n" and "n \<le> t"
          hence " \<tau> n sig = 0"
            by (metis (full_types) Suc.prems(3) domIff not_le to_trans_raw_sig_def zero_option_def)
          thus "to_trans_raw_bit def \<tau> b sig n sig = 0"
            unfolding to_trans_raw_bit_def by (auto split:option.splits simp add: zero_option_def)
        next
          show "Suc a' \<le> t"
            by (simp add: Suc.prems(2))
        qed
        moreover have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig (Suc a') = 
                      signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig a'"
          using signal_of_less_sig 
          using \<open>to_trans_raw_bit def \<tau> b sig (Suc a') sig = None\<close> signal_of_suc_sig zero_option_def by fastforce
        ultimately have ?case
          by auto }
      ultimately have ?case
        by auto }
    moreover
    { assume "\<tau> (Suc a') sig = None"
      hence "signal_of def \<tau> sig (Suc a') = signal_of def \<tau> sig a'"
        using signal_of_less_sig signal_of_suc_sig zero_option_def by fastforce
      hence h0: "to_bit b (signal_of def \<tau> sig a') = v"
        using Suc(2) by auto
      have "to_trans_raw_bit def \<tau> b sig (Suc a') sig = None"
        by (simp add: \<open>\<tau> (Suc a') sig = None\<close> to_trans_raw_bit_def)
      have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig a' = v"
        using Suc(1)[OF h0 order.refl] by auto
      moreover have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig t = 
                     signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig (Suc a')"
      proof (rule signal_of_less_ind')    
        fix n
        assume "Suc a' < n" and "n \<le> t"
        hence " \<tau> n sig = 0"
          by (metis (full_types) Suc.prems(3) domIff not_le to_trans_raw_sig_def zero_option_def)
        thus "to_trans_raw_bit def \<tau> b sig n sig = 0"
          unfolding to_trans_raw_bit_def by (auto split:option.splits simp add: zero_option_def)
      next  
        show "Suc a' \<le> t"
          by (simp add: Suc.prems(2))
      qed
      moreover have "signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig (Suc a') = 
                    signal_of (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit def \<tau> b sig) sig a'"
        using signal_of_less_sig 
        using \<open>to_trans_raw_bit def \<tau> b sig (Suc a') sig = None\<close> signal_of_suc_sig zero_option_def by fastforce      
      ultimately have ?case
        by auto }
    ultimately show ?case 
      by auto
  qed
qed

lemma to_bit_signal_of'_eq:
  "signal_of (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b \<Rightarrow> b)) (to_trans_raw_bit def \<tau> b sig) sig t = v \<longleftrightarrow> to_bit b (signal_of def \<tau> sig t) = v"
  by (metis to_bit_signal_of')

lemma to_bit_signal_of'_eq_simple:
  "signal_of (Bv (case def of Lv sign bs \<Rightarrow> bs ! b | Bv b \<Rightarrow> b)) (to_trans_raw_bit def \<tau> b sig) sig t = to_bit b (signal_of def \<tau> sig t)"
  using to_bit_signal_of' by fastforce

lemma signal_of_inr_post2'_lv:
  assumes "now \<le> t"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  assumes "\<sigma> s \<noteq> Lv sign bs" and "signal_of (\<sigma> s) \<tau> s (now + dly) = Lv sign bs"
  assumes "t < (LEAST n. n \<le> now + dly \<and> (\<exists>b \<in> set [0..< length bs] . to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b))))"
  assumes "t < now + dly"
  shows "signal_of (\<sigma> s) (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)"
  using assms
proof (cases "inf_time (to_trans_raw_sig (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly)) s t = None")
  case True
  then show ?thesis 
    unfolding to_signal_def comp_def by auto
next
  let ?time = "GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some (Lv sign bs)"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) s (now + dly)"
  have 0: "signal_of (\<sigma> s) \<tau> s now \<noteq> Lv sign bs"
    using assms(2-3)  by (metis signal_of_val_eq zero_fun_def zero_option_def)
  have 1: "signal_of (\<sigma> s) \<tau> s (now + dly) = Lv sign bs"
    using assms(4)  by auto
  have "?k2 = Some ?time"
    using earlier_post_time[of "\<sigma>", OF 0 1 assms(2)] by auto
  have "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some (Lv sign bs)"
    using switch_signal_ex_mapping[of "\<sigma>", OF 0 1] assms(2)
    by (simp add: zero_fun_def)
  hence "?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly"
    using GreatestI_ex_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some (Lv sign bs)" and b="now + dly"]
    unfolding keys_def to_trans_raw_sig_def
    by (metis (mono_tags, lifting) CollectI option.simps(3) zero_option_def)
  case False
  then obtain wit where wit: "inf_time (to_trans_raw_sig (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly)) s t = Some wit"
    by auto
  hence "wit = (GREATEST l. l \<in> keys (to_trans_raw_sig (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s) \<and> l \<le> t)"
    using inf_time_when_exist[OF wit] by auto
  moreover have "\<exists>l. l \<in> keys (to_trans_raw_sig (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s) \<and> l \<le> t"
    using False  by (meson inf_time_ex2)
  ultimately have "wit \<in> keys (to_trans_raw_sig (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s)" and "wit \<le> t"
    using inf_time_some_exists wit by force+
  hence inr_none: "inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly wit s \<noteq> None"
    unfolding to_trans_raw_sig_def keys_def  by (simp add: zero_option_def)
  hence "post_raw s (Lv sign bs) (purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs)) (now + dly) wit s \<noteq> None"
    using inr_none unfolding inr_post_raw'_def trans_post_raw_def
    by (smt fun_upd_same less_or_eq_imp_le post_raw_def preempt_raw_def)
  have len_help: "length (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> n s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]) \<le> length bs - 0" 
    by auto
  have "wit \<ge> now + dly \<or> wit < now + dly"
    by auto
  moreover
  { assume "wit \<ge> now + dly"
    hence "wit = now + dly"
      by (metis (full_types) \<open>post_raw s (Lv sign bs) (purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs)) (now + dly) wit s \<noteq> None\<close> fun_upd_same le_imp_less_or_eq post_raw_def)
    with \<open>t < now + dly\<close> have False
      using \<open>wit \<le> t\<close> leD by blast
    hence "signal_of (\<sigma> s) (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s t = \<sigma> s"
      by auto }
  moreover
  { assume "wit < now + dly"
    hence "purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs) wit s \<noteq> None"
      using \<open>post_raw s (Lv sign bs) (purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs)) (now + dly) wit s \<noteq> None\<close>
      unfolding post_raw_def by auto
    hence "combine_trans_bit \<tau>
        (zip (map (\<lambda>n. Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> n s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])) sign s
        now dly wit s \<noteq> None"
      unfolding purge_raw'_def by auto
    moreover have "now \<le> wit"
      by (metis \<open>purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs) wit s \<noteq> None\<close> assms(2) nat_le_linear purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
    moreover have "now < t + dly"
      using \<open>\<exists>n>now. n \<le> now + dly \<and> \<tau> n s = Some (Lv sign bs)\<close> assms(1) by linarith
    ultimately have "wit \<in> fold (\<union>)
          (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd)
            (zip (map (\<lambda>n. Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> n s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs])))
          {}"
      unfolding combine_trans_bit_def 
      by (metis \<open>wit < now + dly\<close> assms(2) dual_order.asym zero_fun_def zero_option_def)
    hence "wit \<in> fold (\<union>) (map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) (map (\<lambda>n. purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> n s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (bs ! n))) [0..<length bs]))) {}"
      unfolding map_map[THEN sym] map_snd_zip_take length_map min.idem length_upt take_all[OF len_help]
      by auto
    hence "\<exists>x\<in>{0..<length bs}. wit \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> x s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (bs ! x))) s)"
      unfolding member_fold_union2 by auto
    then obtain b where "b < length bs" and "wit \<in> keys (to_trans_raw_sig (purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> b s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b))) s)"
      by auto
    hence "purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> b s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) wit s \<noteq> None"
      unfolding keys_def to_trans_raw_sig_def by (auto simp add: zero_option_def)
    moreover have "now < wit"
      by (metis \<open>now \<le> wit\<close> \<open>purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs) wit s \<noteq> None\<close> assms(2)
      le_neq_implies_less purge_raw_before_now_unchanged' zero_fun_def zero_option_def)
    ultimately have "Some wit = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)"
                and h1: "signal_of (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> s) \<tau> b s) s now \<noteq> Bv (bs ! b)" 
                and h2: "signal_of (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (to_trans_raw_bit (\<sigma> s) \<tau> b s) s (now + dly) = Bv (bs ! b)"
      using \<open>wit < now + dly\<close> unfolding purge_raw_def
      by (metis \<open>purge_raw (to_trans_raw_bit (\<sigma> s) \<tau> b s) now dly s (Bv (case \<sigma> s of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! b)) (Bv (bs ! b)) wit s \<noteq> None\<close> purge_raw_neq_0_imp zero_option_def)+
    have h3: "\<And>n. n \<le> now \<Longrightarrow> to_trans_raw_bit (\<sigma> s) \<tau> b s n = 0"
      using \<open>\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0\<close> unfolding to_trans_raw_bit_def zero_fun_def zero_option_def by auto 
    have "inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly) = Some (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))"
      using earlier_post_time_general[OF h1 h2 h3] by auto
    hence "the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)) = (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))"  
      by auto
    also have "... \<ge> (LEAST n. n \<le> now + dly \<and> (\<exists>b \<in> set [0..< length bs] . to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b))))"
    proof -
      have "(GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b))) \<le> now + dly"
        using \<open>inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly) = Some (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))\<close> inf_time_at_most by fastforce
      moreover have "(\<exists>ba \<in> set [0..< length bs] . to_trans_raw_bit (\<sigma> s) \<tau> ba s ((GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))) s = Some (Bv (bs ! ba)))"
        apply (intro bexI[where x="b"])
      proof -
        have f1: "\<forall>f. dom (f::nat \<Rightarrow> val option) = keys f"
          by (simp add: dom_def keys_def zero_option_def)
        have "the (to_trans_raw_bit (\<sigma> s) \<tau> b s wit s) = Bv (bs ! b)"
          by (metis (no_types) \<open>Some wit = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)\<close> h2 o_apply option.simps(5) to_signal_def to_trans_raw_sig_def)
        then show "to_trans_raw_bit (\<sigma> s) \<tau> b s (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b))) s = Some (Bv (bs ! b))"
          using f1 by (metis (no_types) \<open>Some wit = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)\<close> \<open>the (inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)) = (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))\<close> domIff inf_time_some_exists option.collapse option.sel to_trans_raw_sig_def)
      next
        show "b \<in> set [0..<length bs]"
          by (simp add: \<open>b < length bs\<close>)
      qed
      ultimately show "(LEAST n. n \<le> now + dly \<and> (\<exists>b\<in>set [0..<length bs]. to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b))))
    \<le> (GREATEST n. n \<le> now + dly \<and> to_trans_raw_bit (\<sigma> s) \<tau> b s n s = Some (Bv (bs ! b)))"
        by (intro Least_le) auto
    qed
    finally have False
      by (metis (no_types, lifting) \<open>Some wit = inf_time (to_trans_raw_sig (to_trans_raw_bit (\<sigma> s) \<tau> b s)) s (now + dly)\<close> \<open>wit \<le> t\<close> assms(5) dual_order.strict_trans2 leD option.sel)
    hence "signal_of (\<sigma> s) (inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly) s t = \<sigma> s"
      by auto }
  ultimately show ?thesis 
    by auto
qed

lemma signal_of_inr_post3:
  assumes "now \<le> t" and "t < now + dly"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  assumes "signal_of (\<sigma> s) \<tau> s now = v \<or> signal_of (\<sigma> s) \<tau> s (now + dly) \<noteq> v"
  shows "signal_of (\<sigma> s) (inr_post_raw s v (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)" (is "signal_of _ ?inr_post _ _ = _")
proof -
  have "?inr_post = trans_post_raw s v (\<sigma> s) (purge_raw \<tau> now dly s (\<sigma> s) v) now dly" (is "_ = ?trans_post")
    unfolding inr_post_raw_def by auto
  moreover have "purge_raw \<tau> now dly s (\<sigma> s) v = override_on \<tau> (\<lambda>n. (\<tau> n)(s := None)) {now<..now + dly}"
    unfolding purge_raw_def using assms(4) by auto
  ultimately have  "\<And>n. now < n \<Longrightarrow> n < now + dly \<Longrightarrow> ?inr_post n s = 0"
    unfolding trans_post_raw_def
    by (cases "post_necessary_raw (dly - 1) (purge_raw \<tau> now dly s (\<sigma> s) v) now s v (\<sigma> s)")
       (auto simp add: preempt_raw_def post_raw_def zero_option_def)
  with assms(3) have *: "\<And>n. n < now + dly \<Longrightarrow> ?inr_post n s = 0"
    by (metis (full_types) inr_post_raw_def leI purge_raw_before_now_unchanged to_trans_raw_sig_def
    trans_post_less zero_fun_def)
  have "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = None"
    unfolding sym[OF inf_time_none_iff]
  proof
    fix x
    assume "x \<in> dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)"
    hence "?inr_post x s \<noteq> None"
      by (simp add: domIff to_trans_raw_sig_def)
    with * have "now + dly \<le> x"
      by (metis leI zero_option_def)
    thus "t < x"
      using assms(2) by linarith
  qed
  thus ?thesis
    unfolding to_signal_def comp_def by auto
qed

lemma signal_of_inr_post4:
  assumes "signal_of (\<sigma> s) \<tau> s now \<noteq> v" and "signal_of (\<sigma> s) \<tau> s (now + dly) = v"
  assumes "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> t"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  shows "signal_of (\<sigma> s) (inr_post_raw s v (\<sigma> s) \<tau> now dly) s t = v" (is "signal_of _ ?inr_post _ _ = _")
proof -
  have *: "\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v"
  proof (rule ccontr)
    assume "\<not> (\<exists>n. now < n \<and> n \<le> now + dly \<and> \<tau> n s = Some v)"
    hence 0: "\<forall>n. now < n \<and> n \<le> now + dly \<longrightarrow> \<tau> n s = None \<or> \<tau> n s \<noteq> Some v"
      by fastforce
    hence "signal_of (\<sigma> s) \<tau> s (now + dly) \<noteq> v"
    proof (cases "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = None")
      case True
      have "inf_time (to_trans_raw_sig \<tau>) s now = None"
        unfolding sym[OF inf_time_none_iff] using assms(4)
        by (metis True domIff dual_order.trans inf_time_noneE2 le_add1 not_le_imp_less zero_option_def)
      hence "\<sigma> s \<noteq> v"
        using assms(1)
        unfolding to_signal_def comp_def by auto
      then show ?thesis
        unfolding to_signal_def comp_def using True by auto
    next
      case False
      then obtain time where inf: "inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some time"
        by auto
      hence "time \<in> keys (to_trans_raw_sig \<tau> s) \<and> time \<le> now + dly"
        using inf_time_some_exists by fastforce
      hence "\<tau> time s \<noteq> None" and "time \<le> now + dly"
        unfolding keys_def to_trans_raw_sig_def  by (simp add: zero_option_def)+
      hence "now < time"
        using assms(4)  by (metis leI zero_fun_def zero_option_def)
      with \<open>time \<le> now + dly\<close> have "\<tau> time s \<noteq> Some v"
        using 0 \<open>\<tau> time s \<noteq> None\<close> by auto
      then show ?thesis
        unfolding to_signal_def comp_def using inf
        by (metis \<open>\<tau> time s \<noteq> None\<close> option.exhaust_sel option.simps(5) to_trans_raw_sig_def)
    qed
    with assms(2) show False
      by auto
  qed
  have inr_post_alt_def: "?inr_post = trans_post_raw s v (\<sigma> s) (purge_raw \<tau> now dly s (\<sigma> s) v) now dly" (is "_ = ?trans_post")
    unfolding inr_post_raw_def by auto
  let ?purge_raw = "purge_raw \<tau> now dly s (\<sigma> s) v"
  let ?time = "GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v"
  let ?k2 = "inf_time (to_trans_raw_sig \<tau>) s (now + dly)"
  have purge_raw_alt_def: "?purge_raw = override_on \<tau> (\<lambda>n. (\<tau> n)(s := None)) ({now<..<the ?k2} \<union> {the ?k2<..now + dly})"
    unfolding purge_raw_def Let_def using assms(1-2) by auto
  have "?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly"
    using * GreatestI_ex_nat[where P="\<lambda>x. x \<le> now + dly \<and> \<tau> x s = Some v" and b="now + dly"]
    unfolding keys_def to_trans_raw_sig_def
    by (metis (mono_tags, lifting) CollectI option.simps(3) zero_option_def)
  hence "\<tau> ?time s = Some v"
    by (smt "*" GreatestI_nat)
  hence "now < ?time"
    using assms(4)
    by (metis (no_types, lifting) leI option.simps(3) zero_fun_def zero_option_def)
  have "?k2 = Some ?time"
    using earlier_post_time[of "\<sigma>", OF assms(1) assms(2) assms(4)] by auto
  hence "\<forall>j > ?time. j \<le> now + dly \<longrightarrow> to_trans_raw_sig \<tau> s j = None"
    by (meson domIff inf_time_someE leD)
  have "?purge_raw ?time s = Some v"
    using `\<tau> ?time s = Some v` unfolding purge_raw_alt_def `?k2 = Some ?time`
    by auto
  have "\<forall>j > ?time. j \<le> now + dly \<longrightarrow> ?purge_raw j s = None"
    unfolding purge_raw_alt_def `?k2 = Some ?time` by simp
  have "?time < now + dly \<or> ?time  = now + dly"
    using \<open>?time \<in> keys (to_trans_raw_sig \<tau> s) \<and> ?time \<le> now + dly\<close> by auto
  moreover
  { assume "?time < now + dly"
    hence not_nec:  "\<not> post_necessary_raw (dly - 1) (purge_raw \<tau> now dly s (\<sigma> s) v) now s v (\<sigma> s) "
      using `now < ?time` `?time < now + dly` `?purge_raw ?time s = Some v`
      `\<forall>j > ?time. j \<le> now + dly \<longrightarrow> ?purge_raw j s = None`
      unfolding post_necessary_raw_correctness  by (intro disjI1, intro exI[where x="?time"]) auto
    hence "trans_post_raw s v (\<sigma> s) ?purge_raw now dly ?time s = preempt_raw s (purge_raw \<tau> now dly s (\<sigma> s) v) (now + dly) ?time s"
      unfolding trans_post_raw_def by auto
    also have "... = ?purge_raw ?time s"
      using `?time < now + dly` unfolding preempt_raw_def by auto
    also have "... = Some v"
      using \<open>?purge_raw ?time s = Some v\<close> by auto
    finally have "trans_post_raw s v (\<sigma> s) ?purge_raw now dly ?time s = Some v"
      by auto
    hence "?inr_post ?time s = Some v"
      unfolding inr_post_alt_def by auto
    have "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = Some ?time"
    proof (rule inf_time_someI)
      show "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<in> dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)"
        using `?inr_post ?time s = Some v`  by (simp add: domIff to_trans_raw_sig_def)
    next
      show "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> t"
        using assms(3) by blast
    next
      { fix ta
        assume "ta\<in> dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)"
        hence "?inr_post ta s \<noteq> None"
          by (simp add: domIff to_trans_raw_sig_def)
        assume "ta \<le> t"
        have "ta \<le> ?time"
        proof (rule ccontr)
          assume "\<not> ta \<le> ?time"
          hence "?time < ta"
            by auto
          hence "?inr_post ta s = preempt_raw s (purge_raw \<tau> now dly s (\<sigma> s) v) (now + dly) ta s"
            using not_nec unfolding inr_post_alt_def trans_post_raw_def by auto
          also have "... = None"
            unfolding preempt_raw_def
            by (simp add: \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) < ta\<close> \<open>\<forall>j>GREATEST n. n \<le>
            now + dly \<and> \<tau> n s = Some v. j \<le> now + dly \<longrightarrow> purge_raw \<tau> now dly s (\<sigma> s) v j s = None\<close>)
          finally have "?inr_post ta s = None"
            by auto
          with \<open>?inr_post ta s \<noteq> None\<close> show False by auto
        qed }
      thus "\<forall>ta\<in>dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s). ta \<le> t \<longrightarrow> ta \<le> (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
        by auto
    qed
    hence ?thesis
      unfolding to_signal_def comp_def using \<open>?inr_post ?time s = Some v\<close>
      by (simp add: to_trans_raw_sig_def) }
  moreover
  { assume "?time = now + dly"
    have nec:  "post_necessary_raw (dly - 1) (purge_raw \<tau> now dly s (\<sigma> s) v) now s v (\<sigma> s) "
    proof -
      from assms(1) have "signal_of (\<sigma> s) \<tau> s now \<noteq> v"
        by auto
      with signal_of_elim  obtain m where "m \<le> now" and
        "\<tau> m s \<noteq> Some v \<and> (\<forall>j>m. j \<le> now \<longrightarrow> \<tau> j s = None) \<or> (\<forall>i\<le>now. \<tau> i s = None) \<and> v \<noteq> \<sigma> s "
        unfolding to_trans_raw_sig_def
        by (metis assms(1) assms(4) signal_of_def zero_fun_def zero_option_def)
      with assms(4) have "\<tau> now s \<noteq> Some v \<or> v \<noteq> \<sigma> s"
        by auto
      hence "?purge_raw now s \<noteq> Some v \<or> v \<noteq> \<sigma> s"
        unfolding purge_raw_alt_def
        by (metis (full_types) order_refl purge_raw_alt_def purge_raw_before_now_unchanged)
      moreover
      { assume "?purge_raw now s \<noteq> Some v"
        hence ?thesis
          using purge_raw_alt_def unfolding post_necessary_raw_correctness2
          by (smt Suc_diff_1 \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) = now + dly\<close> \<open>(GREATEST
          n. n \<le> now + dly \<and> \<tau> n s = Some v) \<in> keys (to_trans_raw_sig \<tau> s) \<and> (GREATEST n. n \<le> now +
          dly \<and> \<tau> n s = Some v) \<le> now + dly\<close> \<open>inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some
          (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)\<close> \<open>now < (GREATEST n. n \<le> now + dly \<and> \<tau> n s =
          Some v)\<close> add_Suc_right add_diff_cancel_left' assms(1) assms(4) fun_upd_eqD fun_upd_triv
          greaterThanAtMost_empty greaterThanLessThan_iff le_imp_less_Suc not_le option.sel
          override_on_def signal_of_def sup_bot.right_neutral zero_fun_def zero_less_diff
          zero_option_def) }
      moreover
      { assume "v \<noteq> \<sigma> s"
        hence ?thesis
          using purge_raw_alt_def unfolding post_necessary_raw_correctness2
          by (smt Suc_diff_1 Un_iff \<open>(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) = now + dly\<close>
          \<open>inf_time (to_trans_raw_sig \<tau>) s (now + dly) = Some (GREATEST n. n \<le> now + dly \<and> \<tau> n s =
          Some v)\<close> \<open>now < (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)\<close> add_Suc_right
          add_diff_cancel_left' assms(4) fun_upd_same greaterThanLessThan_iff le_imp_less_Suc
          not_less option.sel override_on_apply_in override_on_apply_notin zero_fun_def
          zero_less_diff zero_option_def) }
      ultimately show ?thesis
        by auto
    qed
    hence "trans_post_raw s v (\<sigma> s) ?purge_raw now dly (now + dly) s =
           post_raw s v (purge_raw \<tau> now dly s (\<sigma> s) v) (now + dly) (now + dly) s"
      unfolding trans_post_raw_def by auto
    also have "... = Some v"
      unfolding post_raw_def by auto
    finally have "trans_post_raw s v (\<sigma> s) ?purge_raw now dly (now + dly) s = Some v"
      by auto
    hence "?inr_post ?time s = Some v"
      unfolding inr_post_alt_def \<open>?time = now + dly\<close> by auto
    have "inf_time (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly)) s t = Some ?time"
    proof (rule inf_time_someI)
      show "?time \<in> dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)"
        using `?inr_post ?time s = Some v`  by (simp add: domIff to_trans_raw_sig_def)
    next
      show "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v) \<le> t"
        by (simp add: assms(3))
    next
      { fix ta
        assume "ta\<in>dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)"
        assume "ta \<le> t"
        have "ta \<le> now + dly"
        proof (rule ccontr)
          assume "\<not> (ta \<le> now + dly)"
          hence "now + dly < ta"
            by auto
          hence "inr_post_raw s v (\<sigma> s) \<tau> now dly ta s = None"
            unfolding inr_post_alt_def trans_post_raw_def post_raw_def
            using nec by auto
          with \<open>ta\<in>dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s)\<close> show False
            by (metis domD option.distinct(1) to_trans_raw_sig_def)
        qed }
      thus " \<forall>ta\<in>dom (to_trans_raw_sig (inr_post_raw s v (\<sigma> s) \<tau> now dly) s). ta \<le> t \<longrightarrow> ta \<le> (GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some v)"
        unfolding `?time = now + dly` by auto
    qed
    hence ?thesis
      unfolding to_signal_def comp_def using \<open>?inr_post ?time s = Some v\<close>
      by (simp add: to_trans_raw_sig_def) }
  ultimately show ?thesis
    by auto
qed

lemma signal_of_inr_post4'_bv:
  assumes "signal_of (\<sigma> s) \<tau> s now \<noteq> Bv b" and "signal_of (\<sigma> s) \<tau> s (now + dly) = Bv b"
  assumes "(GREATEST n. n \<le> now + dly \<and> \<tau> n s = Some (Bv b)) \<le> t"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  shows "signal_of (\<sigma> s) (inr_post_raw' s (Bv b) (\<sigma> s) \<tau> now dly) s t = (Bv b)" 
proof -
  have "inr_post_raw' s (Bv b) (\<sigma> s) \<tau> now dly = inr_post_raw s (Bv b) (\<sigma> s) \<tau> now dly"
    unfolding inr_post_raw'_def inr_post_raw_def purge_raw'_def by auto
  moreover have "signal_of (\<sigma> s) (inr_post_raw s (Bv b) (\<sigma> s) \<tau> now dly) s t = (Bv b)"
    using signal_of_inr_post4[where v="Bv b" and \<tau>="\<tau>" and s="s" and now="now" and \<sigma>="\<sigma>", OF assms(1-4)]
    by auto
  ultimately show ?thesis
    by auto
qed

lemma b_seq_exec_preserve_trans_removal:
  assumes "b_seq_exec t \<sigma> \<gamma> def \<theta> ss \<tau> \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t  \<Longrightarrow> \<tau>' n = 0"
  using assms
  by (induction rule:b_seq_exec.induct)
     (auto simp add: trans_post_preserve_trans_removal inr_post_preserve_trans_removal')

lemma b_seq_exec_preserve_trans_removal_nonstrict:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0"
  assumes "nonneg_delay ss"
  shows "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
  using assms
  by (induction rule:b_seq_exec.induct)
     (auto simp add: trans_post_preserve_trans_removal_nonstrict inr_post_preserve_trans_removal_nonstrict')

lemma b_seq_exec_modifies_local:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_in ss) \<Longrightarrow> i \<ge> t  \<Longrightarrow> \<tau> i s =  \<tau>' i s"
  using assms
proof (induction rule:b_seq_exec.induct)
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  hence "s \<notin> set (signals_in ss1)" and "s \<notin> set (signals_in ss2)"
    by auto
  then show ?case using 2 by auto
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case by auto
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case by auto
next
  case (5 t \<sigma> \<gamma> \<theta> def x2 x x1 \<tau> x3 \<tau>')
  hence "s \<noteq> x1" by auto
  have "trans_post_raw x1 x (\<sigma> x1) \<tau> t x3 = \<tau>'"
    using 5 by auto
  then show ?case using `s \<noteq> x1`
    by (metis to_trans_raw_sig_def trans_post_raw_diff_sig)
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence "s \<noteq> sig" by auto
  have inr_post: "inr_post_raw' sig x (\<sigma> sig) \<tau> t dly = \<tau>'"
    using 6 by auto
  hence "\<tau>' = trans_post_raw sig x (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) x) t dly"
    using inr_post unfolding inr_post_raw'_def by auto
  then show ?case using `s \<noteq> sig`
    by (metis inr_post_raw'_def inr_post_raw_does_not_affect_other_sig')
qed (auto)

lemma b_seq_exec_modifies_local_before_now:
  assumes "b_seq_exec t \<sigma> \<gamma> def \<theta> ss \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_in ss) \<Longrightarrow> i < t  \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms
proof (induction rule:b_seq_exec.induct)
  case (2 t \<sigma> \<gamma> \<theta> ss1 \<tau> \<tau>'' ss2 \<tau>')
  then show ?case by auto
next
  case (3 t \<sigma> \<gamma> \<theta> guard ss1 \<tau> \<tau>' ss2)
  then show ?case by auto
next
  case (4 t \<sigma> \<gamma> \<theta> guard ss2 \<tau> \<tau>' ss1)
  then show ?case by auto
next
  case (5 t \<sigma> \<gamma> \<theta> e x sig \<tau> dly \<tau>')
  then show ?case
    by (metis insertCI list.simps(15) signals_in.simps(2) to_trans_raw_sig_def trans_post_raw_diff_sig)
next
  case (6 t \<sigma> \<gamma> \<theta> e x sig \<tau> dly \<tau>')
  then show ?case
    by (metis inr_post_raw_does_not_affect_other_sig' list.set_intros(1) signals_in.simps(3))
qed (auto)

lemma b_seq_exec_modifies_local':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  shows "\<And>s. s \<notin> set (signals_in ss) \<Longrightarrow> \<tau> i s = \<tau>' i s"
  using assms
  by (metis b_seq_exec_modifies_local b_seq_exec_preserve_trans_removal not_le)

lemma b_seq_exec_modifies_local_strongest:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
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

lemma clean_zip_raw_almost_all_zero:
  fixes f g1 g2 :: "nat \<Rightarrow> 'signal \<Rightarrow> val option"
  assumes "\<forall>\<^sub>\<infinity>x. f  x = 0"
  assumes "\<forall>\<^sub>\<infinity>x. g1 x = 0"
  assumes "\<forall>\<^sub>\<infinity>x. g2 x = 0"
  shows   "\<forall>\<^sub>\<infinity>x. clean_zip_raw f (g1, s1) (g2,s2) x = 0"
proof -
  have "\<And>i. g2 i = 0 \<Longrightarrow> f i = 0 \<Longrightarrow> (\<lambda>s. if s \<in> s2 then g2 i s else f i s) = 0"
    unfolding zero_fun_def by (rule ext) auto
  hence "\<forall>\<^sub>\<infinity>i. (\<lambda>s. if s \<in> s2 then g2 i s else f i s) = 0"
    using eventually_elim2[where F="cofinite" and P="\<lambda>x. g2 x = 0" and Q="\<lambda>x. f x = 0"
                          and R="\<lambda>x. (\<lambda>s. if s \<in> s2 then g2 x s else f x s) = 0"]
    assms by auto
  moreover have "\<And>i. g1 i = 0 \<Longrightarrow> (\<lambda>s. if s \<in> s2 then g2 i s else f i s) = 0 \<Longrightarrow>
                              (\<lambda>s. if s \<in> s1 then g1 i s else if s \<in> s2 then g2 i s else f i s) = 0"
    unfolding zero_fun_def by (rule ext) meson
  ultimately show ?thesis
    unfolding clean_zip_raw_def Let_def
    using eventually_elim2[where F="cofinite" and P="\<lambda>x. g1 x = 0" and
                      Q="\<lambda>x. (\<lambda>s. if s \<in> s2 then g2 x s else f x s) = 0" and
                      R="\<lambda>x. (\<lambda>s. if s \<in> s1 then g1 x s else if s \<in> s2 then g2 x s else f x s) = 0",
                      OF assms(2)]
    by auto
qed

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
      using \<open>x \<in> dom (map_diff_trans_raw (clean_zip_raw \<tau> (\<tau>', s') (\<tau>'', s'')) \<tau> n)\<close>  by metis
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

inductive b_conc_exec :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal history \<Rightarrow> 'signal state \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  ("_ , _ , _ , _, _  \<turnstile> <_ , _> \<longrightarrow>\<^sub>c _")
  where
  "disjnt sl \<gamma> \<Longrightarrow> b_conc_exec t \<sigma> \<gamma> \<theta>  def (process sl : ss) \<tau> \<tau>"

| "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow> \<not> disjnt sl \<gamma> \<Longrightarrow>
                                                     b_conc_exec t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"
| "b_conc_exec t \<sigma> \<gamma> \<theta> def  cs1 \<tau> \<tau>1 \<Longrightarrow> b_conc_exec t \<sigma> \<gamma> \<theta> def  cs2 \<tau> \<tau>2 \<Longrightarrow>
    clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'
                                                      \<Longrightarrow> b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"

inductive_cases conc_cases[elim!]:
  "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> <(process sl : ss), \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"

inductive_cases conc_cases_comb:
  "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"

lemma b_conc_exec_deterministic_weaker:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
  assumes "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows   "\<tau>2 = \<tau>1"
  using assms
  apply (induction arbitrary:\<tau>2 \<theta>2 rule:b_conc_exec.induct)
  using b_seq_exec_deterministic_weaker by blast+

lemma b_conc_exec_deterministic:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
  shows "\<tau>2 = \<tau>1"
  using assms b_conc_exec_deterministic_weaker by fastforce

lemma obtain_clean_zip:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
  shows "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'"
  using conc_cases(2)[OF assms(1)] b_conc_exec_deterministic
  by (metis assms(2) assms(3))

lemma b_conc_exec_almost_all_zero:
  assumes "b_conc_exec t  \<sigma>  \<gamma>  \<theta> def cs \<tau> \<tau>'"
  assumes "finite {x. \<tau> x \<noteq> 0}"
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. \<tau>' x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
  by (induction rule:b_conc_exec.induct)
     (auto simp add: clean_zip_raw_almost_all_zero b_seq_exec_almost_all_zero)

theorem conc_stmts_modify_local_only_raw:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  shows "\<And>n. dom (map_diff (\<tau>' n) (\<tau> n)) \<subseteq> set (signals_from cs)"
  using assms
proof (induction rule:b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using seq_stmts_modify_local_only_raw by fastforce
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  then show ?case
    by (smt UnCI UnE dom_map_diff_clean_zip_union set_append signals_from.simps(2) subset_iff)
qed

text \<open>Similar to @{thm "seq_stmts_modify_local_only"}, we also prove that the semantics of the
concurrent statements only modifies the local variables.\<close>

theorem conc_stmts_modify_local_only:
  assumes "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  shows "\<And>n. dom (map_diff_trans_raw \<tau>' \<tau> n) \<subseteq> set (signals_from cs)"
  using assms conc_stmts_modify_local_only_raw by metis

lemma parallel_comp_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs2 || cs1) \<tau> \<tau>'"
proof -
  have *: "disjnt (set (signals_from cs1)) (set (signals_from cs2))"
    using assms(1) unfolding conc_stmt_wf_def by (simp add: disjnt_def)
  show ?thesis
    using van_tassel_second_prop'[OF *] assms(2) b_conc_exec.intros(3) by fastforce
qed

text \<open>The first property we prove for the semantics of the concurrent statement is that two
processes are commutative.\<close>

theorem parallel_comp_commute:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "(t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<longleftrightarrow> (t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
proof
  assume *: " t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs1 || cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 || cs1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  by (simp add: assms parallel_comp_commute')
next
  have assms': "conc_stmt_wf (cs2 || cs1)"
    using assms unfolding conc_stmt_wf_def by auto
  assume *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 || cs1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>' "
    by (simp add: assms' parallel_comp_commute')
qed

lemma clean_zip_raw_assoc:
  "clean_zip_raw \<tau> (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2), s1 \<union> s2) (\<tau>3, s3) =
   clean_zip_raw \<tau> (\<tau>1, s1) (clean_zip_raw \<tau> (\<tau>2, s2) (\<tau>3, s3), (s2 \<union> s3))"
  unfolding clean_zip_raw_def Let_def by (auto intro!: ext)

text \<open>The second property of the semantics of concurrent statements: they are associative. Together
with the first property of being commutative, they in some sense provide a guarantee that they are
truly parallel; we can execute whichever process in any order and the merging will always be the
same.\<close>

theorem parallel_comp_assoc:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs2) || cs3) \<tau> \<tau>'"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || (cs2 || cs3)) \<tau> \<tau>'"
proof (rule conc_cases(2)[OF assms])
  fix \<tau>1 \<tau>2
  assume *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
  then obtain \<tau>1a \<tau>1b where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1a" and  "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1b"
    by blast+
  hence **: "clean_zip_raw \<tau> (\<tau>1a, set (signals_from cs1)) (\<tau>1b, set (signals_from cs2)) = \<tau>1"
    using obtain_clean_zip[OF *] by auto
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
  assume "clean_zip_raw \<tau> (\<tau>1, set (signals_from (cs1 || cs2))) (\<tau>2, set (signals_from cs3)) = \<tau>'"
  hence "clean_zip_raw \<tau> (\<tau>1a, set (signals_from cs1)) (clean_zip_raw \<tau> (\<tau>1b, set (signals_from cs2)) (\<tau>2, set (signals_from cs3)), (set (signals_from cs2) \<union> set (signals_from cs3))) = \<tau>'"
    unfolding sym[OF **] using clean_zip_raw_assoc[of "\<tau>" "\<tau>1a" "set (signals_from cs1)" "\<tau>1b" "set (signals_from cs2)" "\<tau>2" "set (signals_from cs3)"]
    by auto
  thus "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || (cs2 || cs3) , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (metis \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1a\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1b\<close> \<open>t
    , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2\<close> b_conc_exec.intros(3) set_append signals_from.simps(2))
qed

theorem parallel_comp_assoc2:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || (cs2 || cs3)) \<tau> \<tau>'"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs2) || cs3) \<tau> \<tau>'"
  using assms
  by (smt b_conc_exec.intros(3) clean_zip_raw_assoc conc_cases(2) set_append signals_from.simps(2))

lemma b_conc_exec_distrib1:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs3) || (cs2 || cs3)) \<tau> \<tau>'"
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs2) || cs3) \<tau> \<tau>'"
proof (rule conc_cases(2)[OF assms(1)])
  fix \<tau>13 \<tau>23 
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>13"
  then obtain \<tau>1 \<tau>3 where h0: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1" and tau3: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>3" 
    and h1: "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>3, set (signals_from cs3)) = \<tau>13"
    by (rule conc_cases(2)) blast
  assume tau23: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>23"
  then obtain \<tau>2 where tau2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2" and 
                       h2: "clean_zip_raw \<tau> (\<tau>2, set (signals_from cs2)) (\<tau>3, set (signals_from cs3)) = \<tau>23"
    apply (rule conc_cases(2))
    using tau3 b_conc_exec_deterministic by blast
  obtain \<tau>12 where tau12: "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>12"
    by blast
  assume *: "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) = \<tau>'"
  have "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) = \<tau>'"
    unfolding *[symmetric]
  proof (rule ext, rule ext)
    fix t s
    consider "s \<in> set (signals_from cs1)" 
      | " s \<in> set (signals_from cs2)"
      | " s \<in> set (signals_from cs3) " 
      | " s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2) \<and> s \<notin> set  (signals_from cs3)"
      by auto
    thus "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = 
          clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s"
    proof (cases)
      case 1
      hence " clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>1 t s"
        by (smt UnCI \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>12\<close> clean_zip_raw_def prod.simps(2) set_append signals_from.simps(2))
      moreover have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>1 t s"
        using 1 h0 tau3 h1  by (smt "*" assms b_conc_exec_deterministic clean_zip_raw_def conc_cases(2) parallel_comp_assoc prod.simps(2))
      ultimately show ?thesis 
        by auto
    next
      case 2
      hence "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>2 t s"
        using h0 tau3 h1
        by (smt IntI UnCI \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>12\<close> assms(2) clean_zip_raw_def conc_stmt_wf_def distinct_append emptyE prod.simps(2) set_append signals_from.simps(2))
      moreover have " clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>2 t s"
      proof -
        have "s \<notin> set (signals_from (cs1 || cs3))"
          using 2 assms(2)  by (metis IntI Un_iff conc_stmt_wf_def distinct_append emptyE set_append signals_from.simps(2))
        moreover have "s \<in> set (signals_from (cs2 || cs3))"
          using 2 by auto
        ultimately have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>23 t s"
          unfolding clean_zip_raw_def Let_def by (auto)
        also have "... = \<tau>2 t s"
          using h2 2 unfolding clean_zip_raw_def Let_def by auto
        finally show ?thesis
          by auto
      qed
      ultimately show ?thesis 
        by auto
    next
      case 3
      hence " clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>3 t s"
        unfolding clean_zip_raw_def Let_def 
        by (smt IntI assms(2) case_prod_conv conc_stmt_wf_def distinct_append emptyE signals_from.simps(2))
      moreover have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>3 t s"
      proof -
        have "s \<in> set (signals_from (cs1 || cs3))" and "s \<notin> set (signals_from cs1)"
          using 3  apply auto
          using assms(2) 3  by (metis (full_types) IntI UnCI conc_stmt_wf_def distinct_append emptyE set_append signals_from.simps(2))
        hence "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>13 t s"
          unfolding clean_zip_raw_def Let_def by auto
        also have "... = \<tau>3 t s"
          using h1 3 `s \<notin> set (signals_from cs1)`unfolding clean_zip_raw_def Let_def by auto
        finally show ?thesis
          by auto
      qed
      ultimately show ?thesis 
        by auto
    next
      case 4
      hence "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau> t s"
        by (simp add: clean_zip_raw_def)
      moreover have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau> t s"
        using 4 by (simp add: clean_zip_raw_def)
      ultimately show ?thesis 
        by auto
    qed
  qed
  thus " t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(cs1 || cs2) || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (metis \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>12\<close> \<open>t ,
    \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs2 || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>23\<close> b_conc_exec.intros(3) clean_zip_raw_assoc h0 h2
    parallel_comp_assoc2 set_append signals_from.simps(2))
qed

lemma b_conc_exec_distrib2:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs2) || cs3) \<tau> \<tau>'"
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows  "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs3) || (cs2 || cs3)) \<tau> \<tau>'"
proof (rule conc_cases(2)[OF assms(1)])
  fix \<tau>12 \<tau>3 
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1 || cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>12"
  then obtain \<tau>1 \<tau>2 where h0: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>1" and tau3: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2" 
    and h1: "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>12"
    by (rule conc_cases(2)) blast
  assume tau3':"t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>3"
  obtain \<tau>13 where "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>3, set (signals_from cs3)) = \<tau>13"
    by blast
  obtain \<tau>23 where tau23: "clean_zip_raw \<tau> (\<tau>2, set (signals_from cs2)) (\<tau>3, set (signals_from cs3)) = \<tau>23"
    by blast
  assume *: "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) = \<tau>'"
  have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) = \<tau>'"
    unfolding *[symmetric]
  proof (rule ext, rule ext)
    fix t s
    consider "s \<in> set (signals_from cs1)" 
      | " s \<in> set (signals_from cs2)"
      | " s \<in> set (signals_from cs3) " 
      | " s \<notin> set (signals_from cs1) \<and> s \<notin> set (signals_from cs2) \<and> s \<notin> set  (signals_from cs3)"
      by auto
    thus "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = 
          clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s"
    proof (cases)
      case 1
      hence " clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s  = \<tau>1 t s"
        by (smt UnCI \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>3, set (signals_from cs3)) = \<tau>13\<close> clean_zip_raw_def prod.simps(2) set_append signals_from.simps(2))
      moreover have "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>1 t s"
        using 1    by (smt "*" assms(1) b_conc_exec_deterministic clean_zip_raw_def conc_cases(2) h0 parallel_comp_assoc prod.simps(2))
      ultimately show ?thesis 
        by auto
    next
      case 2
      hence " s \<notin> set (signals_from (cs1 || cs3))" and "s \<in> set (signals_from (cs2 || cs3))"
        using assms(2) 2 by (metis IntI Un_iff conc_stmt_wf_def distinct_append emptyE set_append signals_from.simps(2))+
      hence "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s  = \<tau>23 t s"
        by (simp add: clean_zip_raw_def)
      also have "... = \<tau>2 t s"
        unfolding tau23[symmetric] clean_zip_raw_def using 2  by simp
      finally have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s  = \<tau>2 t s"
        by auto
      moreover have " clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>2 t s"
        using 2 assms(2)  by (smt UnCI \<open>s \<notin> set (signals_from (cs1 || cs3))\<close> clean_zip_raw_def h1 prod.simps(2) set_append signals_from.simps(2))
      ultimately show ?thesis 
        by auto
    next
      case 3
      hence " clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau>3 t s"
        by (smt IntI assms(2) case_prod_conv clean_zip_raw_def conc_stmt_wf_def distinct_append emptyE signals_from.simps(2))
      moreover have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau>3 t s"
        using 3  by (smt IntI UnCI UnI1 \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>3, set (signals_from cs3)) = \<tau>13\<close> tau3' append.assoc append_Nil2 append_assoc assms(1) assms(2) b_conc_exec_deterministic case_prod_conv clean_zip_raw_def conc_cases(2) conc_stmt_wf_def distinct_append emptyE in_set_conv_decomp prod.simps(1) prod.simps(2) set_append signals_from.simps(2))
      ultimately show ?thesis 
        by auto
    next
      case 4
      hence "clean_zip_raw \<tau> (\<tau>12, set (signals_from (cs1 || cs2))) (\<tau>3, set (signals_from cs3)) t s = \<tau> t s"
        by (simp add: clean_zip_raw_def)
      moreover have "clean_zip_raw \<tau> (\<tau>13, set (signals_from (cs1 || cs3))) (\<tau>23, set (signals_from (cs2 || cs3))) t s = \<tau> t s"
        using 4 by (simp add: clean_zip_raw_def)
      ultimately show ?thesis 
        by auto
    qed
  qed
  thus "  t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(cs1 || cs3) || cs2 || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (metis \<open>clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>3, set (signals_from cs3)) = \<tau>13\<close> b_conc_exec.intros(3) h0 tau23 tau3 tau3')
qed

lemma parallel_composition_distrib:
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows "b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs2) || cs3) \<tau> \<tau>' \<longleftrightarrow> b_conc_exec t \<sigma> \<gamma> \<theta> def ((cs1 || cs3) || (cs2 || cs3)) \<tau> \<tau>'"
  using b_conc_exec_distrib1[OF _ assms] b_conc_exec_distrib2[OF _ assms] 
  by meson

text \<open>The Language Reference Manual for VHDL stipulates that each process will be executed initially
regardless of their sensitivity list.\<close>

inductive init' :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal history \<Rightarrow>  'signal state \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool" where
   "t, \<sigma>, \<gamma>, \<theta>, def  \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>' \<Longrightarrow> init' t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"
|  "init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 \<Longrightarrow> init' t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2 \<Longrightarrow>
  clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>' \<Longrightarrow> init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"


inductive_cases init'_cases[elim!] :
  "init' t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"
  "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"

lemma init'_deterministic:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>1"
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>2"
  shows "\<tau>2 = \<tau>1"
  using assms
  apply (induction arbitrary:\<tau>2 rule:init'.induct)
  using b_seq_exec_deterministic by blast+

lemma init'_par_obtain_constituent_trans:
  assumes "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  obtains \<tau>1 \<tau>2 where "init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1" and "init' t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2"
                      "clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'"
  using init'_cases(2)[OF assms]  by metis

lemma init'_raw_almost_all_zero:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "finite {x. \<theta> x \<noteq> 0}"
  assumes "finite {x. \<tau> x \<noteq> 0}"
  shows "finite {x. \<tau>' x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
  by (induction rule:init'.induct)
     (auto simp add: clean_zip_raw_almost_all_zero b_seq_exec_almost_all_zero)

lemma init'_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  shows "init' t \<sigma> \<gamma> \<theta> def (cs2 || cs1) \<tau> \<tau>'"
proof -
  have *: "disjnt (set (signals_from cs1)) (set (signals_from cs2))"
    using assms(1) unfolding conc_stmt_wf_def by (simp add: disjnt_def)
  show ?thesis
    using van_tassel_second_prop'[OF *] assms(2) init'.intros(2) by fastforce
qed

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
    using assms el  unfolding to_trans_raw_sig_def  by (simp add: domIff)
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

lemma clean_zip_raw_preserve_trans_removal_nonstrict:
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>  n = 0"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0"
  assumes "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
  shows "\<And>n. n \<le> t \<Longrightarrow> (clean_zip_raw \<tau> (\<tau>1,s1) (\<tau>2,s2)) n = 0"
  using assms  unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)

lemma b_conc_exec_preserve_trans_removal:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
  using assms
  apply (induction rule:b_conc_exec.induct)
  apply blast
  apply (simp add: b_seq_exec_preserve_trans_removal)
  using clean_zip_raw_preserve_trans_removal by blast

lemma b_conc_exec_preserve_trans_removal_nonstrict:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "nonneg_delay_conc cs"
  shows   "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
  using assms
proof (induction rule:b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_preserve_trans_removal_nonstrict nonneg_delay_conc.simps(1) by blast
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0" and "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0" and "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
    by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)))"
    using 3 b_conc_exec.intros(3) by blast
  have "\<And>n. n \<le> t \<Longrightarrow>  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) n = 0"
    using clean_zip_raw_preserve_trans_removal_nonstrict
    using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0\<close> \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0\<close> by blast
  then show ?case
    using 3(3) 3(6) by auto
qed

lemma init'_preserves_trans_removal:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "nonneg_delay_conc cs"
  shows   "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
  using assms
proof (induction rule:init'.induct)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_preserve_trans_removal_nonstrict nonneg_delay_conc.simps(1) by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0" and "\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0" and "\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0"
    by auto
  have "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)))"
    using 2  init'.intros(2) by blast
  have "\<And>n. n \<le> t \<Longrightarrow>  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) n = 0"
    using clean_zip_raw_preserve_trans_removal_nonstrict
    using \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau>1 n = 0\<close> \<open>\<And>n. n \<le> t \<Longrightarrow> \<tau>2 n = 0\<close> by blast
  then show ?case
    using 2 by auto
qed

lemma init'_preserves_trans_removal_strict:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
  using assms
proof (induction rule:init'.induct)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_preserve_trans_removal  by blast    
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "\<And>n. n < t \<Longrightarrow> \<tau> n = 0" and "\<And>n. n < t \<Longrightarrow> \<tau>1 n = 0" and "\<And>n. n < t \<Longrightarrow> \<tau>2 n = 0"
    by auto
  have "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)))"
    using 2  init'.intros(2) by blast
  have "\<And>n. n < t \<Longrightarrow>  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) n = 0"
    using clean_zip_raw_preserve_trans_removal
    using \<open>\<And>n. n < t \<Longrightarrow> \<tau> n = 0\<close> \<open>\<And>n. n < t \<Longrightarrow> \<tau>1 n = 0\<close> \<open>\<And>n. n < t \<Longrightarrow> \<tau>2 n = 0\<close> by blast
  then show ?case
    using 2 by auto
qed

lemma  rem_curr_trans_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow>  (\<tau>(t:=0)) n = 0"
  using assms by auto

lemma b_conc_exec_rem_curr_trans_preserve_trans_removal:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>(t:=0)> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
  using assms
  by (simp add: b_conc_exec_preserve_trans_removal rem_curr_trans_preserve_trans_removal)

lemma b_conc_exec_modifies_local:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def  cs \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i \<ge> t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
proof (induction rule:b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_modifies_local_strongest by fastforce
next
  case (3 t \<sigma> \<gamma> \<theta> def  cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using 3 `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using `s \<notin> set (signals_from cs2)` 3 `i \<ge> t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by (simp add: clean_zip_raw_def)
  then show ?case
    using "3.hyps"(3) by blast
qed

lemma init'_modifies_local:
  assumes "init' t \<sigma> \<gamma> \<theta> def  cs \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i \<ge> t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
proof (induction rule: init'.induct)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_modifies_local by fastforce
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using 2 `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using 2 `s \<notin> set (signals_from cs2)` `i \<ge> t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by ( simp add: clean_zip_raw_def)
  then show ?case
    using "2.hyps"(3) by blast
qed

lemma b_conc_exec_modifies_local_before_now:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i < t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
proof (induction rule:b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def  ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def  ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_modifies_local_before_now by fastforce
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using 3 `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using 3 `s \<notin> set (signals_from cs2)` `i < t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by (simp add: clean_zip_raw_def)
  then show ?case
    using "3.hyps"(3) by blast
qed

lemma init'_modifies_local_before_now:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i < t \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
proof (induction rule:init'.induct)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_modifies_local_before_now by fastforce
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  hence " \<tau> i s =  \<tau>1 i s"
    using 2 `s \<notin> set (signals_from cs1)` by blast
  moreover have " \<tau> i s =  \<tau>2 i s"
    using 2`s \<notin> set (signals_from cs2)` `i < t` by blast
  ultimately have " \<tau> i s =  (clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))) i s"
    by ( simp add: clean_zip_raw_def)
  then show ?case
    using "2.hyps"(3) by blast
qed

lemma b_conc_exec_modifies_local':
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  using assms
  by (metis b_conc_exec_modifies_local b_conc_exec_preserve_trans_removal not_le)

lemma b_conc_exec_modifies_local_strongest:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def  cs \<tau> \<tau>'"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  by (metis assms b_conc_exec_modifies_local b_conc_exec_modifies_local_before_now not_le)

lemma init'_modifies_local_strongest:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow>  \<tau> i s =  \<tau>' i s"
  by (metis assms init'_modifies_local init'_modifies_local_before_now not_le)

lemma b_conc_exec_empty_event:
  "b_conc_exec t \<sigma> {} \<theta> def  cs \<tau> \<tau>"
proof (induction cs)
  case (Bpar cs1 cs2)
  then show ?case
    using clean_zip_same by (auto intro!: b_conc_exec.intros)
next
  case (Bsingle x1 x2)
  then show ?case  by (simp add: b_conc_exec.intros(1))
qed

fun disjnts where
  "disjnts \<gamma> (Bsingle sl ss) \<longleftrightarrow> disjnt \<gamma> sl"
| "disjnts \<gamma> (Bpar cs1 cs2) \<longleftrightarrow> disjnts \<gamma> cs1 \<and> disjnts \<gamma> cs2"

lemma b_conc_exec_disjnts_event:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "disjnts \<gamma> cs"
  shows "\<tau> = \<tau>'"
  using assms
proof (induction cs arbitrary:\<tau>')
  case (Bpar cs1 cs2)
  then show ?case
    by (metis clean_zip_same conc_cases(2) disjnts.simps(2))
next
  case (Bsingle x1 x2)
  then show ?case
    using disjnt_sym disjnts.simps(1) by blast
qed

lemma b_conc_exec_trans_unchanged:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<gamma> = {} \<or> disjnts \<gamma> cs"
  shows "\<tau> = \<tau>'"
  using assms b_conc_exec_empty_event b_conc_exec_disjnts_event
  by (metis b_conc_exec_deterministic)

lemma b_seq_exec_trans_post_raw_same:
  fixes sig e dly
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau>1 \<tau>1'"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  assumes ss_def: "ss = Bassign_trans sig e dly"
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau>1' k s =   \<tau>' k s"
proof -
  fix k s
  assume "s \<in> set (signals_in ss)"
  hence "s = sig"
    using assms by auto
  obtain v where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b v"
    using assms(2) ss_def  by (meson seq_cases_trans)
  hence "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bassign_trans sig e dly) \<tau>1 (trans_post_raw sig v (\<sigma> sig) \<tau>1 t dly)"
    by (meson b_seq_exec.intros(5))
  have "trans_post_raw sig v (\<sigma> sig) \<tau>1 t dly k s =  (trans_post_raw sig v (\<sigma> sig) \<tau> t dly) k s"
  proof -
    have "post_necessary_raw (dly-1) \<tau>1 t sig v = post_necessary_raw (dly-1) \<tau> t sig v"
      using assms `s \<in> set (signals_in ss)`
      by (metis \<open>s = sig\<close> signal_of_equal_when_trans_sig_equal_upto to_trans_raw_sig_def)
    moreover have "preempt_raw sig \<tau>1 (t + dly) k s = preempt_raw sig \<tau> (t + dly) k s"
      using assms unfolding preempt_raw_def using `s = sig`  by simp
    moreover have "post_raw sig v \<tau>1 (t + dly) k s = post_raw sig v \<tau> (t + dly) k s"
      using assms unfolding post_raw_def using `s = sig` by auto
    ultimately show ?thesis
      unfolding trans_post_raw_def  by smt
  qed
  thus "\<tau>1' k s =   \<tau>' k s"
    by (metis assms \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b v\<close> beval_raw_deterministic seq_cases_trans)
qed

lemma purge_raw_equal_signal:
  fixes \<tau>1 \<tau>2 :: "'a trans_raw"
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  shows "\<And>k. purge_raw \<tau>1 t dly s def val k s = purge_raw \<tau>2 t dly s def val k s"
proof -
  fix k
  let ?k  = "inf_time (to_trans_raw_sig \<tau>1) s (t + dly)"
  let ?k' = "inf_time (to_trans_raw_sig \<tau>2) s (t + dly)"
  have "?k = ?k'"
  proof -
    have " (\<exists>k\<in>keys (to_trans_raw_sig \<tau>1 s). k \<le> t + dly) \<longleftrightarrow>
           (\<exists>k\<in>keys (to_trans_raw_sig \<tau>2 s). k \<le> t + dly)"
      using assms unfolding to_trans_raw_sig_def keys_def by simp
    moreover hence "(GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>1 s) \<and> k \<le> t + dly) =
           (GREATEST k. k \<in> keys (to_trans_raw_sig \<tau>2 s) \<and> k \<le> t + dly)"
      by (simp add: assms to_trans_raw_sig_def)
    ultimately show ?thesis
      unfolding inf_time_def by auto
  qed
  let ?s1 = "signal_of def \<tau>1 s t"
  let ?s2 = "signal_of def \<tau>1 s (t + dly)"
  let ?s1' = "signal_of def \<tau>2 s t"
  let ?s2' = "signal_of def \<tau>2 s (t + dly)"
  have "?s1 = ?s1'"
    using assms
    by (intro signal_of_equal_when_trans_sig_equal_upto) (auto simp add: to_trans_raw_sig_def)
  have "?s2 = ?s2'"
    using assms
    by (intro signal_of_equal_when_trans_sig_equal_upto) (auto simp add: to_trans_raw_sig_def)
  have "override_on \<tau>1 (\<lambda>n. (\<tau>1 n)(s := None)) {t <.. t + dly} k s =
        override_on \<tau>2 (\<lambda>n. (\<tau>2 n)(s := None)) {t <.. t + dly} k s"
    using assms
    by (metis (mono_tags, lifting) fun_upd_same override_on_apply_in override_on_apply_notin)
  moreover
  have " override_on \<tau>1 (\<lambda>n. (\<tau>1 n)(s := None)) ({t <..< the ?k} \<union> {the ?k <.. t + dly}) k s =
         override_on \<tau>2 (\<lambda>n. (\<tau>2 n)(s := None)) ({t <..< the ?k'} \<union> {the ?k' <.. t + dly}) k s"
    unfolding `?k = ?k'` using assms
    by (smt fun_upd_apply override_on_apply_in override_on_apply_notin)
  ultimately show "purge_raw \<tau>1 t dly s def val k s = purge_raw \<tau>2 t dly s def val k s"
    using `?s1 = ?s1'` `?s2 = ?s2'` unfolding purge_raw_def Let_def by auto
qed

lemma combine_trans_bit_equal_signal':
  fixes \<tau>1 \<tau>2 :: "'a trans_raw"
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  assumes "\<And>k. t < k \<Longrightarrow> k \<le> t + dly \<Longrightarrow> map (\<lambda>p. bval_of (to_signal (fst p) (to_trans_raw_sig (snd p)) s k)) \<tau>s1 = 
                                          map (\<lambda>p. bval_of (to_signal (fst p) (to_trans_raw_sig (snd p)) s k)) \<tau>s2"
  assumes "fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd) \<tau>s1) {} = 
           fold (\<union>) (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd) \<tau>s2) {}"
  shows "\<And>k. combine_trans_bit \<tau>1 \<tau>s1 sign s t dly k s = combine_trans_bit \<tau>2 \<tau>s2 sign s t dly k s"
  unfolding combine_trans_bit_def Let_def
  using assms by (auto)

lemma combine_trans_bit_equal_signal:
  fixes \<tau>1 \<tau>2 :: "'a trans_raw"
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  shows "\<And>k. combine_trans_bit \<tau>1 \<tau>s sign s t dly k s = combine_trans_bit \<tau>2 \<tau>s sign s t dly k s"
  unfolding combine_trans_bit_def Let_def
  using assms by auto

(* TODO: terribly ugly proof! *)
lemma purge_raw_equal_signal':
  fixes \<tau>1 \<tau>2 :: "'a trans_raw"
  assumes "\<And>k. \<tau>1 k s = \<tau>2 k s"
  shows "\<And>k. purge_raw' \<tau>1 t dly s def val k s = purge_raw' \<tau>2 t dly s def val k s"
proof (induction val)
  case (Bv x)
  then show ?case 
    unfolding purge_raw'_def using purge_raw_equal_signal[ of "\<tau>1" _ "\<tau>2", OF assms]
    by (auto simp add: )
next
  case (Lv x1a x2)
  have 0: "\<And>n k. (to_trans_raw_bit def \<tau>1 n s) k s = (to_trans_raw_bit def \<tau>2 n s) k s"
    unfolding to_trans_raw_bit_def 
    using assms
    by (smt comp_apply diff_le_self option.case_eq_if to_signal_equal_when_trans_equal_upto2)
  have *: "\<And>x y. (to_signal x (to_trans_raw_sig (purge_raw (to_trans_raw_bit def \<tau>1 y s) t dly s (Bv (lval_of def ! y)) (Bv (x2 ! y)))) s k) = 
               (to_signal x (to_trans_raw_sig (purge_raw (to_trans_raw_bit def \<tau>2 y s) t dly s (Bv (lval_of def ! y)) (Bv (x2 ! y)))) s k)"
    using to_signal_equal_when_trans_equal_upto2 assms
    by (metis "0" dual_order.refl purge_raw_equal_signal)    
  have **: "(take (length x2) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>1 n s) t dly s (Bv (lval_of def ! n)) (Bv (x2 ! n))) [0..<length x2])) = 
        (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>1 n s) t dly s (Bv (lval_of def ! n)) (Bv (x2 ! n))) [0..<length x2])"
    by auto
  have ***: "(take (length x2) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>2 n s) t dly s (Bv (lval_of def ! n)) (Bv (x2 ! n))) [0..<length x2])) = 
        (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>2 n s) t dly s (Bv (lval_of def ! n)) (Bv (x2 ! n))) [0..<length x2])"
    by auto
  have 4: "\<And>n x . purge_raw (to_trans_raw_bit def \<tau>1 x s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (x2 ! x)) n s = 
                  purge_raw (to_trans_raw_bit def \<tau>2 x s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! x)) (Bv (x2 ! x)) n s"
    apply (intro purge_raw_equal_signal)
    using 0 by auto
  hence "map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>1 n s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (x2 ! n))) [0..<length x2])) =
        map keys (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>2 n s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (x2 ! n))) [0..<length x2]))"
    unfolding map_map comp_def to_trans_raw_sig_def map_eq_conv  by auto
  hence 5: "(map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd)
       (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length x2]) 
            (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>1 n s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (x2 ! n))) [0..<length x2]))) = 
        (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd)
       (zip (map (\<lambda>n. Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) [0..<length x2]) 
            (map (\<lambda>n. purge_raw (to_trans_raw_bit def \<tau>2 n s) t dly s (Bv (case def of Bv b \<Rightarrow> b | Lv sign bs \<Rightarrow> bs ! n)) (Bv (x2 ! n))) [0..<length x2])))"
    unfolding sym[OF map_map] map_snd_zip_take length_map min.idem length_upt minus_nat.diff_0 ** ***
    by auto
  show ?case 
    unfolding purge_raw'_def 
    apply (auto)
    apply (intro combine_trans_bit_equal_signal')
    using assms(1) apply simp
    unfolding 5
    apply auto
    unfolding map_zip_map2 map_eq_conv fst_conv snd_conv 
     apply (auto split:prod.splits)
    using * 
    by (smt "0" purge_raw_equal_signal to_signal_equal_when_trans_equal_upto2)+
qed

lemma b_seq_exec_inr_post_same:
  fixes sig e dly
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def  ss \<tau>1 \<tau>1'"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
  assumes ss_def: "ss = Bassign_inert sig e dly"
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau>1' k s =   \<tau>' k s"
proof -
  fix k s
  assume "s \<in> set (signals_in ss)"
  hence "s = sig"
    unfolding ss_def by auto
  hence 2: "\<And>k.  \<tau> k s =  \<tau>1 k s"
    using assms unfolding ss_def by auto
  obtain v where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b v"
    using assms(2) ss_def by (meson seq_cases_inert)
  hence 3: "b_seq_exec t \<sigma> \<gamma> \<theta> def (Bassign_inert sig e dly) \<tau>1 (inr_post_raw' sig v (\<sigma> sig) \<tau>1 t dly)"
    by (meson b_seq_exec.intros(6))
  have in_tr: "inr_post_raw'  sig v (\<sigma> sig) \<tau>1 t dly =
        trans_post_raw sig v (\<sigma> sig) (purge_raw' \<tau>1 t dly sig (\<sigma> sig) v) t dly "
    unfolding inr_post_raw'_def by auto
  have *: "\<And>k. (purge_raw' \<tau>1 t dly sig (\<sigma> sig) v) k s = (purge_raw' \<tau> t dly sig (\<sigma> sig) v) k s"
    using 2 `s = sig` purge_raw_equal_signal' by metis
  define purge_rawd1 where "purge_rawd1 = purge_raw' \<tau>1 t dly sig (\<sigma> sig) v"
  define purge_rawd  where "purge_rawd  = purge_raw' \<tau>  t dly sig (\<sigma> sig) v"
  hence "\<And>k.  purge_rawd1 k s =  purge_rawd k s"
    using * unfolding purge_rawd1_def by auto
  hence tr_tr: " (trans_post_raw sig v (\<sigma> sig) purge_rawd1 t dly) k s =
         (trans_post_raw sig v (\<sigma> sig) purge_rawd t dly) k s "
    using `s = sig`
  proof -
    have "post_necessary_raw (dly-1) purge_rawd1 t sig v (\<sigma> sig) =
          post_necessary_raw (dly-1) purge_rawd t sig v (\<sigma> sig)"
      using post_necessary_raw_same[of "purge_rawd1" "s" "purge_rawd"] *
      by (simp add: \<open>s = sig\<close> purge_rawd1_def purge_rawd_def)
    thus ?thesis
      by (smt "*" \<open>s = sig\<close> fun_upd_same preempt_raw_def purge_rawd1_def purge_rawd_def
      post_raw_def trans_post_raw_def)
  qed
  have " \<tau>1' k s = (inr_post_raw'  sig v (\<sigma> sig) \<tau>1 t dly) k s"
    by (metis "3" assms(1) b_seq_exec_deterministic ss_def)
  also have "... =   (trans_post_raw sig v (\<sigma> sig) (purge_raw' \<tau>1 t dly sig (\<sigma> sig) v) t dly) k s"
    using in_tr by auto
  also have "... =   (trans_post_raw sig v (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) v) t dly) k s"
    using tr_tr unfolding purge_rawd1_def purge_rawd_def by auto
  also have "... =   (inr_post_raw'  sig v (\<sigma> sig) \<tau> t dly) k s"
    unfolding inr_post_raw'_def by auto
  also have "... =  \<tau>' k s"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> e \<longrightarrow>\<^sub>b v\<close> assms(2) beval_raw_deterministic ss_def
    by (metis b_seq_exec.intros(6) b_seq_exec_deterministic)
  finally show " \<tau>1' k s = \<tau>' k s"
    by auto
qed

lemma b_seq_exec_same:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau>1 \<tau>1''"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>''"
  assumes "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  shows "\<And>k s. s \<in> set (signals_in ss) \<Longrightarrow>  \<tau>1'' k s =  \<tau>'' k s"
  using assms
proof (induction arbitrary: \<tau> \<tau>'' rule:b_seq_exec.induct)
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau>1 \<tau>' choices)
  have *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>''"
    apply (rule seq_cases_bcase[OF 7(6), rotated])
    by (metis "7.hyps"(1) "7.hyps"(2) Pair_inject beval_raw_deterministic choices.inject list.inject) auto
  have **: "\<And>sa k. sa \<in> signals_of ss \<Longrightarrow> \<tau> k sa = \<tau>1 k sa"
  proof -
    fix sa k
    assume "sa \<in> signals_of ss"
    hence  "sa \<in> signals_of (Bcase exp ((Explicit exp', ss) # choices)) "
      by auto
    thus "\<tau> k sa = \<tau>1 k sa"
      using 7 by auto
  qed
  have "s \<in> signals_of ss \<or> s \<notin> signals_of ss"
    by auto
  moreover
  { assume " s \<in> signals_of ss"
    hence ?case
      using "*" "**" "7.IH" by blast }
  moreover
  { assume " s \<notin> signals_of ss"
    hence "\<tau>' k s = \<tau>1 k s"
      using 7  by (metis \<open>s \<notin> signals_of ss\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>1> \<longrightarrow>\<^sub>s \<tau>'\<close>
      b_seq_exec_modifies_local_strongest)
    also have "... = \<tau> k s"
      using 7 by simp
    also have "... = \<tau>'' k s"
      using \<open>s \<notin> signals_of ss\<close> * by (meson b_seq_exec_modifies_local_strongest)
    finally have ?case
      by auto }
  ultimately show ?case
    by auto
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau>1 \<tau>' ss)
  have *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bcase exp choices , \<tau>> \<longrightarrow>\<^sub>s \<tau>''"
    apply (rule seq_cases_bcase[OF 8(7)])
    by (metis "8.hyps"(1) "8.hyps"(2) "8.hyps"(3) Pair_inject beval_raw_deterministic choices.inject
    list.inject) auto
  have **: "\<And>sa k.  sa \<in> signals_of (Bcase exp choices) \<Longrightarrow> \<tau> k sa = \<tau>1 k sa"
  proof -
    fix sa k
    assume "sa \<in> signals_of (Bcase exp choices)"
    hence " sa \<in> signals_of (Bcase exp ((Explicit exp', ss) # choices))"
      by auto
    with 8 show "\<tau> k sa = \<tau>1 k sa"
      by auto
  qed
  have "s \<in> signals_of (Bcase exp choices) \<or> s \<notin> signals_of (Bcase exp choices)"
    by auto
  moreover
  { assume "s \<in> signals_of (Bcase exp choices)"
    hence ?case
      using "*" "**" "8.IH" by auto }
  moreover
  { assume "s \<notin> signals_of (Bcase exp choices)"
    hence "\<tau>' k s = \<tau> k s"
      using "8.hyps"(4) "8.prems"(1) "8.prems"(3) b_seq_exec_modifies_local_strongest
      by metis
    also have "... = \<tau>'' k s"
      using * \<open>s \<notin> signals_of (Bcase exp choices)\<close>
      by (meson b_seq_exec_modifies_local_strongest)
    finally have ?case
      by auto }
  ultimately show ?case
    by auto
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau>1 \<tau>1' exp choices)
  have *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>''"
    by (rule seq_cases_bcase[OF 9(4)]) auto
  have **: "\<And>sa k. sa \<in> signals_of ss \<Longrightarrow> \<tau> k sa = \<tau>1 k sa"
  proof -
    fix sa k
    assume "sa \<in> signals_of ss"
    hence  "sa \<in> signals_of (Bcase exp ((Others, ss) # choices)) "
      by auto
    thus "\<tau> k sa = \<tau>1 k sa"
      using 9(5) by auto
  qed
  have "s \<in> signals_of ss \<or> s \<notin> signals_of ss"
    by auto
  moreover
  { assume "s \<in> signals_of ss"
    hence ?case
      using "*" "**" "9.IH" by blast }
  moreover
  { assume "s \<notin> signals_of ss"
    hence " \<tau>1' k s = \<tau>1 k s"
      using 9  by (metis b_seq_exec_modifies_local_strongest)
    also have "... = \<tau> k s"
      using 9 by simp
    also have "... = \<tau>'' k s"
      using \<open>s \<notin> signals_of ss\<close> \<open>t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>
    proof -
      have "\<exists>f fa sa fb A n fc. \<tau>1' k s = fc k s \<and> s \<notin> signals_of sa \<and> n , fa , A , f, fb \<turnstile> < sa , fc> \<longrightarrow>\<^sub>s \<tau>''"
        by (metis \<open>s \<notin> signals_of ss\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close> calculation)
      then show ?thesis
        by (metis (no_types) b_seq_exec_modifies_local_strongest calculation)
    qed
    finally have ?case by auto }
  ultimately show ?case
    by auto
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case by auto
next
  case (1 t \<sigma> \<gamma> \<theta> def  \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau>1 \<tau>1' ss2 \<tau>1'')
  then obtain \<tau>' where A: "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>'" and B: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss2 , \<tau>'> \<longrightarrow>\<^sub>s \<tau>''"
    by (meson seq_cases_bcomp)
  have *: "\<And>k s. s \<in> set (signals_in ss1) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s" and
       **: "\<And>k s. s \<in> set (signals_in ss2) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
    using 2 by auto
  hence inss1: "\<And>k s. s \<in> set (signals_in ss1) \<Longrightarrow>  \<tau>' k s =  \<tau>1' k s"
    using 2(3) A 2(1)  by (metis (full_types))
  have ninss1: "\<And>k s. s \<notin> set (signals_in ss1) \<Longrightarrow>  \<tau>' k s =  \<tau> k s"
    using b_seq_exec_modifies_local_strongest[OF `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s \<tau>'`] by auto
  have ninss1': "\<And>k s. s \<notin> set (signals_in ss1) \<Longrightarrow>  \<tau>1' k s =  \<tau>1 k s"
    using b_seq_exec_modifies_local_strongest[OF `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss1, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'`] by auto

  have "s \<in> set (signals_in ss1) \<or> s \<notin> set (signals_in ss1)"
    by auto
  moreover
  { assume "s \<in> set (signals_in ss1)"
    have  " \<tau>' k s =  \<tau>1' k s"
      using 2(3)[OF `s \<in> set (signals_in ss1)` A *] by auto
    hence " \<tau>' k s =  \<tau>1' k s"
      unfolding A * by auto
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
      hence ***: " \<tau>'' k s =  \<tau>1'' k s"
        using 2(4)[OF `s \<in> set (signals_in ss2)` B] by metis
      hence ?case by auto }
    moreover
    { assume "s \<notin> set (signals_in ss2)"
      have "\<tau>'' k s =  \<tau>' k s"
        using `s \<notin> set (signals_in ss2)` b_seq_exec_modifies_local_strongest
        using B by fastforce
      also have "... =  \<tau>1' k s"
        using inss1[OF `s \<in> set (signals_in ss1)`] by auto
      also have "... =  \<tau>1'' k s"
        using `s \<notin> set (signals_in ss2)` b_seq_exec_modifies_local_strongest
        using "2"(2) by fastforce
      finally have ?case by auto }
    ultimately have ?case by auto }
  moreover
  { assume "s \<notin> set (signals_in ss1)"
    hence "s \<in> set (signals_in ss2)"
      using 2 by auto
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
    hence ***: "\<tau>'' k s =  \<tau>1''  k s"
      using 2(4)[OF `s \<in> set (signals_in ss2)` B]  by simp
    hence ?case
      by simp }
  ultimately show ?case
    by auto
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 tau tau' ss2)
  hence "t , \<sigma> , \<gamma> , \<theta> , def \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''"
    using beval_raw_deterministic  by (metis seq_cases_bguarded val.inject(1))
  have "s \<in> signals_of ss1 \<or> s\<notin> signals_of ss1"
    by auto
  moreover
  { assume " s \<in> signals_of ss1"
    hence "\<And>s k. s \<in> signals_of ss1 \<Longrightarrow> \<tau> k s = tau k s"
    proof -
      fix s' k'
      assume "s' \<in> signals_of ss1"
      hence "s' \<in> signals_of (Bguarded guard ss1 ss2)"
        by auto
      thus "\<tau> k' s' = tau k' s'"
        using 3(6) by auto
    qed
    hence "?case"
      using 3(3)[OF \<open>s \<in> signals_of ss1\<close>  \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>] by auto }
  moreover
  { assume "s \<notin> signals_of ss1"
    hence "tau' k s = tau k s"
      using 3(2)  using b_seq_exec_modifies_local_strongest by fastforce
    also have "... = \<tau> k s"
      using 3 by simp
    also have "... = \<tau>'' k s"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>
      by (meson \<open>s \<notin> signals_of ss1\<close> b_seq_exec_modifies_local_strongest)
    finally have "?case"
      by auto }
  ultimately show ?case
    by auto
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 tau tau' ss1)
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''"
    using beval_raw_deterministic  by (metis seq_cases_bguarded val.inject(1))
  have "s \<in> signals_of ss2 \<or> s\<notin> signals_of ss2"
    by auto
  moreover
  { assume " s \<in> signals_of ss2"
    hence "\<And>s k. s \<in> signals_of ss2 \<Longrightarrow> \<tau> k s = tau k s"
    proof -
      fix s' k'
      assume "s' \<in> signals_of ss2"
      hence "s' \<in> signals_of (Bguarded guard ss2 ss2)"
        by auto
      thus "\<tau> k' s' = tau k' s'"
        using 4(6) by auto
    qed
    hence "?case"
      using 4(3)[OF \<open>s \<in> signals_of ss2\<close>  \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>] by auto }
  moreover
  { assume "s \<notin> signals_of ss2"
    hence "tau' k s = tau k s"
      using 4(2)  using b_seq_exec_modifies_local_strongest by fastforce
    also have "... = \<tau> k s"
      using 4 by simp
    also have "... = \<tau>'' k s"
      using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss2 , \<tau>> \<longrightarrow>\<^sub>s \<tau>''\<close>
      by (meson \<open>s \<notin> signals_of ss2\<close> b_seq_exec_modifies_local_strongest)
    finally have "?case"
      by auto }
  ultimately show ?case
    by auto
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig tau dly tau')
  hence *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bassign_trans sig e dly , tau> \<longrightarrow>\<^sub>s tau'"
    by (meson b_seq_exec.intros(5))
  show ?case
    using b_seq_exec_trans_post_raw_same[OF * 5(4) _ 5(5) 5(3)] by auto
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig tau dly tau')
  hence *: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <Bassign_inert sig e dly , tau> \<longrightarrow>\<^sub>s tau'"
    by (meson b_seq_exec.intros(6))
  then show ?case
    using b_seq_exec_inr_post_same[OF * 6(4) _ 6(5) 6(3)] by auto
qed

lemma b_conc_exec_same:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  assumes "conc_stmt_wf cs"
  shows "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  \<tau>1' k s =  \<tau>' k s"
  using assms
proof (induction arbitrary: \<tau> \<tau>' rule: b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    by (smt b_seq_exec_same conc_cases(1) signals_from.simps(1))
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau>1 \<tau>a cs2 \<tau>b \<tau>1')
  hence "conc_stmt_wf cs2" and "conc_stmt_wf cs1"
    by (simp add: conc_stmt_wf_def)+
  note \<tau>a_def = 3(1)
  note \<tau>b_def = 3(2)
  obtain \<tau>a' \<tau>b' where \<tau>a'_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def  cs1 \<tau> \<tau>a'" and \<tau>b'_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def  cs2 \<tau> \<tau>b'" and
    "clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2)) = \<tau>'"
    using "3.prems"(2) by blast
  have "\<And>k.  \<tau> k s =  \<tau>1 k s"
    using 3 by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau>1 (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2)))"
    using \<tau>a_def \<tau>b_def  using b_conc_exec.intros(3) by blast
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2)"
    using 3 by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    hence " (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s =
            \<tau>a k s"
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    also have "... =  \<tau>a' k s"
      using 3(4)[OF `s \<in> set (signals_from cs1)` \<tau>a'_def _ `conc_stmt_wf cs1`] "3.prems"(3)
      by simp
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs1)`
      unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using "3.hyps"(3) \<open>clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2)) = \<tau>'\<close> by blast }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    moreover hence "s \<notin> set (signals_from cs1)"
      using ` conc_stmt_wf (cs1 || cs2)`
      by (metis conc_stmt_wf_def disjnt_def disjnt_iff distinct_append signals_from.simps(2))
    ultimately have " (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s =
            \<tau>b k s"
       unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    also have "... =  \<tau>b' k s"
      using 3(5)[OF `s \<in> set (signals_from cs2)` \<tau>b'_def _ `conc_stmt_wf cs2`]
      by (simp add: "3.prems"(3))
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs2)` `s \<notin> set (signals_from cs1)`
      unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using "3.hyps"(3) \<open>clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2)) = \<tau>'\<close> by blast}
  ultimately  show ?case
    by auto
qed

lemma init'_same:
  assumes "init' t \<sigma> \<gamma> \<theta> def  cs \<tau>1 \<tau>1'"
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
  assumes "conc_stmt_wf cs"
  shows "\<And>k s. s \<in> set (signals_from cs) \<Longrightarrow>  \<tau>1' k s =  \<tau>' k s"
  using assms
proof (induction arbitrary: \<tau> \<tau>' rule:init'.induct)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau>1 \<tau>1' sl)
  hence *: "\<And>k s.  s \<in> set (signals_in ss) \<Longrightarrow>  \<tau> k s =  \<tau>1 k s"
    by auto
  have **: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>'"
    using init'_cases(1)[OF 1(3)] by auto
  have "init' t \<sigma> \<gamma> \<theta> def  (Bsingle sl ss) \<tau>1 \<tau>1'"
    using 1  by (simp add: init'.intros(1))
  have "\<tau>1' k s =  \<tau>' k s"
    using b_seq_exec_same[OF 1(1) ** *] 1 by auto
  also have "... =  \<tau>' k s"
    by auto
  finally show ?case
    using \<open>\<tau>1' k s = \<tau>' k s\<close> by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def  cs1 \<tau>1 \<tau>a cs2 \<tau>b \<tau>cz)
  hence "conc_stmt_wf cs2" and "conc_stmt_wf cs1"
    by (simp add: conc_stmt_wf_def)+
  obtain \<tau>a' \<tau>b' where \<tau>a'_def: " init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>a'" and \<tau>b'_def: " init' t \<sigma> \<gamma> \<theta> def  cs2 \<tau> \<tau>b'" and
    "clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2)) = \<tau>'"
    using init'_cases(2)[OF 2(7)] by auto
  have "\<And>k.  \<tau> k s =  \<tau>1 k s"
    using 2 by auto
  have "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau>1 (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2)))"
    using 2  by (meson init'.intros(2))
  have "s \<in> set (signals_from cs1) \<or> s \<in> set (signals_from cs2)"
    using 2 by auto
  moreover
  { assume "s \<in> set (signals_from cs1)"
    have "\<tau>cz k s =  \<tau>a' k s"
      using 2(4)[OF `s \<in> set (signals_from cs1)` \<tau>a'_def _ `conc_stmt_wf cs1`]
      by (smt "2"(3) "2.prems"(3) UnCI \<open>s \<in> set (signals_from cs1)\<close> clean_zip_raw_def prod.simps(2)
      set_append signals_from.simps(2))
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs1)` unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using \<open>clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2)) = \<tau>'\<close>
      by blast }
  moreover
  { assume "s \<in> set (signals_from cs2)"
    moreover hence "s \<notin> set (signals_from cs1)"
      using ` conc_stmt_wf (cs1 || cs2)`
      by (metis conc_stmt_wf_def disjnt_def disjnt_iff distinct_append signals_from.simps(2))
    ultimately have " (clean_zip_raw \<tau>1 (\<tau>a, set (signals_from cs1)) (\<tau>b, set (signals_from cs2))) k s = \<tau>b k s"
      unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    also have "... =  \<tau>b' k s"
      using 2(5)[OF `s \<in> set (signals_from cs2)` \<tau>b'_def _ `conc_stmt_wf cs2`] by (simp add: "2.prems"(3))
    also have "... =  (clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))) k s"
      using `s \<in> set (signals_from cs2)` `s \<notin> set (signals_from cs1)`
      unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
    finally have ?case
      using "2.hyps"(3) \<open>clean_zip_raw \<tau> (\<tau>a', set (signals_from cs1)) (\<tau>b', set (signals_from cs2))
      = \<tau>'\<close> by blast }
  ultimately show ?case
    by auto
qed

lemma b_conc_exec_sequential':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau>  \<tau>1"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>1 \<tau>''"
  shows "\<tau>' = \<tau>''"
proof -
  have "conc_stmt_wf cs2"
    using assms by (simp add: conc_stmt_wf_def)
  obtain \<tau>2 where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
    using assms(2) by blast
  define s1 where "s1 = set (signals_from cs1)"
  define s2 where "s2 = set (signals_from cs2)"
  have "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2))"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2\<close> assms(3) b_conc_exec.intros(3) s1_def s2_def by
    blast
  also have "... = \<tau>''"
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
      have " \<tau>'' k s =  \<tau>1 k s"
        using \<open>s \<notin> set (signals_from cs2)\<close> assms(4) b_conc_exec_modifies_local_strongest by fastforce
      with * have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
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
        by (metis assms(1) assms(3) b_conc_exec_modifies_local_strongest conc_stmt_wf_def
        disjoint_insert(1) distinct_append mk_disjoint_insert signals_from.simps(2))
      hence " \<tau>'' k s =  \<tau>2 k s"
        using b_conc_exec_same[OF _ _ _ `conc_stmt_wf cs2` `s \<in> set (signals_from cs2)`]
        \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2\<close> assms(4) by auto
      hence " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
        using * by auto }
    moreover
    { assume "s \<notin> s1 \<and> s \<notin> s2"
      hence *: " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau> k s"
         unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
      have "s \<notin> set (signals_from cs2)" and "s \<notin> set (signals_from cs1)"
        using `s \<notin> s1 \<and> s \<notin> s2` unfolding s2_def s1_def by auto
      have " \<tau>'' k s =  \<tau>1 k s"
        using b_conc_exec_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs2)`]
        using assms(4) by fastforce
      also have "... =  \<tau> k s"
        using b_conc_exec_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs1)`] assms(3)
        by fastforce
      finally have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
        using * by auto }
    ultimately show " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
      by auto
  qed
  finally show ?thesis
    by (simp add: assms(2) b_conc_exec_deterministic)
qed

lemma only_context_matters_for_progress:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>1> \<longrightarrow>\<^sub>s \<tau>1'"
  shows   "\<exists>\<tau>2'. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>2> \<longrightarrow>\<^sub>s \<tau>2'"
  using assms
  by (induction arbitrary: \<tau>2 rule:b_seq_exec.inducts)
     (meson b_seq_exec.intros)+

lemma only_context_matters_for_progress_beval:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> exp \<longrightarrow>\<^sub>b res"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows   "\<exists>res2. t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> exp \<longrightarrow>\<^sub>b res2"
  using assms
proof (induction arbitrary: \<theta>2 rule: beval_raw.inducts)
  case (1 now \<sigma> \<gamma> \<theta> def sig)
  then show ?case by (auto intro!:beval_raw.intros)
next
  case (2 now \<sigma> \<gamma> \<theta> def)
  then show ?case by (auto intro!:beval_raw.intros)
next
  case (3 now \<sigma> \<gamma> \<theta> def)
  then show ?case by (auto intro!:beval_raw.intros)
next
  case (4 now \<sigma> \<gamma> \<theta> def sig t)
  then show ?case by (auto intro!:beval_raw.intros)
next
  case (5 now \<sigma> \<gamma> \<theta> def sig)
  then show ?case by (auto intro!:beval_raw.intros)
next
  case (6 now \<sigma> \<gamma> \<theta> def e bool)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Bv bool"
    using beval_raw_deterministic_weaker 6 by blast
  then show ?case 
    by (auto dest: beval_raw_deterministic_weaker intro!: exI[where x="Bv (\<not> bool)"] beval_raw.intros(6))
next
  case (7 now \<sigma> \<gamma> \<theta> def e ki bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Lv ki bs"
    using beval_raw_deterministic_weaker 7 by blast
  then show ?case 
    using beval_raw.intros(7) by blast
next
  case (8 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(8) by blast    
next
  case (9 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(9) by blast
next
  case (10 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(10) by blast    
next
  case (11 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(11) by blast
next
  case (12 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(12) by blast 
next
  case (13 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(13) by blast
next
  case (14 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(14) by blast 
next
  case (15 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(15) by blast 
next
  case (16 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(16) by blast 
next
  case (17 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(17) by blast 
next
  case (18 now \<sigma> \<gamma> \<theta> def e1 val1 e2 val2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Bv val1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Bv val2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(18) by blast 
next
  case (19 now \<sigma> \<gamma> \<theta> def e1 ki bs1 e2 bs2)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv ki bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv ki bs2" and "length bs1 = length bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(19) by blast 
next
  case (20 now \<sigma> \<gamma> \<theta> def sig ki bs len l r)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> Bsig sig \<longrightarrow>\<^sub>b Lv ki bs"
    using beval_raw_deterministic_weaker  by metis
  then show ?case 
    using beval_raw.intros(20) `length bs = len` by metis
next
  case (21 now \<sigma> \<gamma> \<theta> def sig ki bs idx)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> Bsig sig \<longrightarrow>\<^sub>b Lv ki bs"
    using beval_raw_deterministic_weaker  by metis
  then show ?case 
    using beval_raw.intros(21) by metis
next
  case (22 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Uns bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Uns bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(22) 22(3-4) by blast
next
  case (23 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Sig bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Sig bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(23) 23(3-4) by blast
next
  case (24 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Uns bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Uns bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(24) 24(3-4) by blast
next
  case (25 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Sig bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Sig bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(25) 25(3-4) by blast
next
  case (26 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Uns bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Uns bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(26) 26(3-4) by blast
next
  case (27 now \<sigma> \<gamma> \<theta> def e1 bs1 e2 bs2 len bs)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e1 \<longrightarrow>\<^sub>b Lv Sig bs1" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e2 \<longrightarrow>\<^sub>b Lv Sig bs2"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(27) 27(3-4) by blast
next
  case (28 now \<sigma> \<gamma> \<theta> def e bs bs' n)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Lv Uns bs"
    using beval_raw_deterministic_weaker by blast
  then show ?case 
    using beval_raw.intros(28) 28(2) by blast
next
  case (29 now \<sigma> \<gamma> \<theta> def e bs bs' n)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Lv Sig bs"
    using beval_raw_deterministic_weaker by blast
  then show ?case 
    using beval_raw.intros(29) 29(2) by blast 
next
  case (30 now \<sigma> \<gamma> \<theta> def e bs bs' n)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Lv Uns bs"
    using beval_raw_deterministic_weaker by blast
  then show ?case 
    using beval_raw.intros(30) 30(2) by blast
next
  case (31 now \<sigma> \<gamma> \<theta> def e bs bs' n)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b Lv Sig bs"
    using beval_raw_deterministic_weaker by blast
  then show ?case 
    using beval_raw.intros(31) 31(2) by blast
next
  case (32 now \<sigma> \<gamma> \<theta> def guard th res el)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> guard \<longrightarrow>\<^sub>b Bv True" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> th \<longrightarrow>\<^sub>b res"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(32) by blast
next
  case (33 now \<sigma> \<gamma> \<theta> def guard el res th)
  hence "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> guard \<longrightarrow>\<^sub>b Bv False" and "now , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> el \<longrightarrow>\<^sub>b res"
    using beval_raw_deterministic_weaker by blast+
  then show ?case 
    using beval_raw.intros(33) by blast
next
  case (34 now \<sigma> \<gamma> \<theta> def sign val)
  then show ?case 
    using beval_raw.intros(34) by blast
qed
  
lemma only_context_matters_for_progress_hist:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>1'"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows   "\<exists>\<tau>2'. t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>s \<tau>2'"
  using assms
proof (induction arbitrary: \<theta>2 \<tau> rule:b_seq_exec.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by (auto intro!: b_seq_exec.intros)
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  then obtain a a' where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s a" and "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss2 , a> \<longrightarrow>\<^sub>s a'"
    by blast
  thus ?case 
    by (auto intro!: exI[where x="a'"] b_seq_exec.intros)
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau>1 \<tau>' ss2)
  hence "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> guard \<longrightarrow>\<^sub>b a" and ex: "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss1 , \<tau>> \<longrightarrow>\<^sub>s a"
    using only_context_matters_for_progress_beval by blast+
  then obtain a where th: "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> guard \<longrightarrow>\<^sub>b Bv True" and ex': "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss1, \<tau>> \<longrightarrow>\<^sub>s a"
    using beval_raw_deterministic_weaker[OF 3(1)] 3(4) by blast
  thus ?case 
    by (intro exI) (intro b_seq_exec.intros(3)[OF th])     
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau>1 \<tau>' ss1)
  hence "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> guard \<longrightarrow>\<^sub>b a" and ex: "\<exists>a. t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss2 , \<tau>> \<longrightarrow>\<^sub>s a"
    using only_context_matters_for_progress_beval by blast+
  then obtain a where th: "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> guard \<longrightarrow>\<^sub>b Bv False" and ex': "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> < ss2, \<tau>> \<longrightarrow>\<^sub>s a"
    using beval_raw_deterministic_weaker[OF 4(1)] 4(4) by blast
  thus ?case 
    by (intro exI) (intro b_seq_exec.intros(4)[OF th])     
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau>1 dly \<tau>')
  then obtain a where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> e \<longrightarrow>\<^sub>b a"
    using only_context_matters_for_progress_beval by blast
  then show ?case 
    by (auto intro!: b_seq_exec.intros)  
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau>1 dly \<tau>')
  then show ?case 
    by (auto intro!: b_seq_exec.intros dest: only_context_matters_for_progress_beval)  
next
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau>1 \<tau>' choices)
  obtain a where a: "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s a"
    using 7(4)[OF 7(5), of "\<tau>"] by auto
  have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using only_context_matters_for_progress_beval[OF 7(1) 7(5)] beval_raw_deterministic_weaker[OF 7(1) _ 7(5)]
    by blast
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x"
    using only_context_matters_for_progress_beval[OF 7(2) 7(5)] beval_raw_deterministic_weaker[OF 7(2) _ 7(5)]
    by blast
  ultimately show ?case 
    using a by (auto intro!: b_seq_exec.intros)    
next
  case (8 t \<sigma> \<gamma> \<theta> def exp x exp' x' choices \<tau>1 \<tau>' ss)
  obtain a where "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < Bcase exp choices , \<tau>> \<longrightarrow>\<^sub>s a"
    using 8(5)[OF 8(6), of "\<tau>"] by auto
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using only_context_matters_for_progress_beval[OF 8(1) 8(6)] beval_raw_deterministic_weaker[OF 8(1) _ 8(6)]
    by blast
  moreover have "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
    using only_context_matters_for_progress_beval[OF 8(2) 8(6)] beval_raw_deterministic_weaker[OF 8(2) _ 8(6)]
    by blast
  ultimately show ?case 
    using 8(3) by (auto intro!: b_seq_exec.intros(8))
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau>1 \<tau>' exp choices)
  obtain a where " t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s a"
    using 9(2)[OF 9(3)] by blast
  then show ?case 
    by (auto intro!: b_seq_exec.intros(9))
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  then show ?case 
    by (auto intro!: b_seq_exec.intros(10))
qed

lemma only_context_matters_for_progress_conc:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>1> \<longrightarrow>\<^sub>c \<tau>1'"
  shows   "\<exists>\<tau>2'. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>2> \<longrightarrow>\<^sub>c \<tau>2'"
  using assms
proof (induction rule:b_conc_exec.inducts)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case
    using b_conc_exec.intros(1) by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    by (meson b_conc_exec.intros(2) only_context_matters_for_progress)
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  then show ?case
    using b_conc_exec.intros(3) by blast
qed

lemma only_context_matters_for_progress_conc_hist:
  assumes "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>1'"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  shows   "\<exists>\<tau>2'. t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>2'"
  using assms
proof (induction arbitrary: \<theta>2 rule:b_conc_exec.inducts)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case 
    using b_conc_exec.intros(1) by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_conc_exec.intros(2)[OF _ 2(2)]  only_context_matters_for_progress_hist[OF 2(1) 2(3)]
    by blast
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  have " t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs1 , \<tau>> \<longrightarrow>\<^sub>c \<tau>1"
    using 3(4)[OF 3(6)] b_conc_exec_deterministic_weaker[OF _ _ 3(6)] 3(1) by blast
  moreover have " t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs2 , \<tau>> \<longrightarrow>\<^sub>c \<tau>2"
    using 3(5)[OF 3(6)] b_conc_exec_deterministic_weaker[OF _ _ 3(6)] 3(2) by blast
  ultimately show ?case
    using 3 by (auto intro!: b_conc_exec.intros)
qed

lemma only_context_matters_for_progress_init:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau>1 \<tau>1'"
  shows   "\<exists>\<tau>2'. init' t \<sigma> \<gamma> \<theta> def cs \<tau>2 \<tau>2'"
  using assms
  by (induction rule:init'.inducts)
     (metis init'.intros only_context_matters_for_progress)+

lemma b_conc_exec_sequential:
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau>  \<tau>1"
  shows   "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>1 \<tau>'"
  using b_conc_exec_sequential' only_context_matters_for_progress_conc
  by (metis assms(1) assms(2) assms(3) conc_cases(2))


(* text \<open>Execute the sequential statement regardless whether it is quiet or not. This hopefully will 
simplify the Hoare proof effort.\<close>

inductive b_conc_exec2 :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal history \<Rightarrow> 'signal state \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> bool"
  ("_ , _ , _ , _, _  \<turnstile> <_ , _> \<longrightarrow>\<^sub>c2 _")
  where
  "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' \<Longrightarrow>  b_conc_exec2 t \<sigma> \<gamma> \<theta> def (process sl : ss) \<tau> \<tau>'"

| "b_conc_exec2 t \<sigma> \<gamma> \<theta> def  cs1 \<tau> \<tau>1 \<Longrightarrow> b_conc_exec2 t \<sigma> \<gamma> \<theta> def  cs2 \<tau> \<tau>2 \<Longrightarrow>
    clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2)) = \<tau>'
                                                      \<Longrightarrow> b_conc_exec2 t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>>\<longrightarrow>\<^sub>c2 \<tau>'"
  shows   "\<exists>\<tau>2. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>>\<longrightarrow>\<^sub>c \<tau>2"
  using assms
proof (induction rule: b_conc_exec2.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case 
    by (meson b_conc_exec.intros(1) b_conc_exec.intros(2))
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  then show ?case 
    using b_conc_exec.intros(3) by blast
qed

lemma
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>>\<longrightarrow>\<^sub>c  \<tau>2"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>>\<longrightarrow>\<^sub>c2 \<tau>1"
  shows   "\<forall>s k. signal_of (def s) \<tau>1 s k = signal_of (def s) \<tau>2 s k"
  using assms
proof (induction arbitrary: \<tau>1 rule:b_conc_exec.inducts)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  hence "b_seq_exec t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>1"
    using b_conc_exec2.cases by blast
  then show ?case sorry
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case 
    (* by (metis (mono_tags, lifting) b_conc_exec2.simps b_seq_exec_deterministic conc_stmt.sel(4) conc_stmt.simps(4)) *)
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  then show ?case sorry
qed *)

lemma init'_sequential':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  assumes "init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1"
  assumes "init' t \<sigma> \<gamma> \<theta> def cs2 \<tau>1 \<tau>''"
  shows "\<tau>' = \<tau>''"
proof -
  have "conc_stmt_wf cs2"
    using assms by (simp add: conc_stmt_wf_def)
  obtain \<tau>2 where "init' t \<sigma> \<gamma> \<theta> def  cs2 \<tau> \<tau>2"
    using assms(2) by blast
  define s1 where "s1 = set (signals_from cs1)"
  define s2 where "s2 = set (signals_from cs2)"
  have "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2))"
    using \<open>init' t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2\<close> assms(3) init'.intros s1_def s2_def by fastforce
  also have "... = \<tau>''"
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
      have " \<tau>'' k s =  \<tau>1 k s"
        using \<open>s \<notin> set (signals_from cs2)\<close> assms(4) init'_modifies_local_strongest by fastforce
      with * have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
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
        by (metis assms(1) assms(3) init'_modifies_local_strongest conc_stmt_wf_def
        disjoint_insert(1) distinct_append mk_disjoint_insert signals_from.simps(2))
      hence " \<tau>'' k s =  \<tau>2 k s"
        using init'_same[OF _ _ _ `conc_stmt_wf cs2` `s \<in> set (signals_from cs2)`]
        \<open>init' t \<sigma> \<gamma> \<theta> def cs2 \<tau> \<tau>2\<close> assms(4) by auto
      hence " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
        using * by auto }
    moreover
    { assume "s \<notin> s1 \<and> s \<notin> s2"
      hence *: " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau> k s"
         unfolding clean_zip_raw_def Let_def by (auto split:prod.splits)
      have "s \<notin> set (signals_from cs2)" and "s \<notin> set (signals_from cs1)"
        using `s \<notin> s1 \<and> s \<notin> s2` unfolding s2_def s1_def by auto
      have " \<tau>'' k s =  \<tau>1 k s"
        using init'_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs2)`]
        using assms(4) by fastforce
      also have "... =  \<tau> k s"
        using init'_modifies_local_strongest[OF _ ` s \<notin> set (signals_from cs1)`] assms(3)
        by fastforce
      finally have " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
        using * by auto }
    ultimately show " (clean_zip_raw \<tau> (\<tau>1, s1) (\<tau>2, s2)) k s =  \<tau>'' k s"
      by auto
  qed
  finally show ?thesis
    by (simp add: assms(2) init'_deterministic)
qed

lemma init'_sequential:
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "init' t \<sigma> \<gamma> \<theta> def (cs1 || cs2) \<tau> \<tau>'"
  assumes "init' t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1"
  shows   "init' t \<sigma> \<gamma> \<theta> def cs2 \<tau>1 \<tau>'"
  using only_context_matters_for_progress_init init'_sequential'
  by (metis assms(1) assms(2) assms(3) init'_cases(2))

subsection \<open>Types\<close>

datatype ty =
    Bty     (* scalar of boolean *)
  | Lty signedness nat (* vector / array  of booleans *)

type_synonym 's tyenv = "'s \<Rightarrow> ty"

inductive bexp_wt :: "'s tyenv \<Rightarrow> 's bexp \<Rightarrow> ty \<Rightarrow> bool" where
  "bexp_wt \<Gamma> Btrue Bty"
| "bexp_wt \<Gamma> Bfalse Bty"
| "ty = \<Gamma> sig \<Longrightarrow> bexp_wt \<Gamma> (Bsig sig) ty"
| "bexp_wt \<Gamma> (Bsig_event sig) Bty"
| "bexp_wt \<Gamma> (Bsig_delayed sig dly) (\<Gamma> sig)"
| "bexp_wt \<Gamma> exp type  \<Longrightarrow> bexp_wt \<Gamma> (Bnot exp) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Band exp1 exp2) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Bor exp1 exp2) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Bnand exp1 exp2) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Bnor exp1 exp2) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Bxor exp1 exp2) type"
| "bexp_wt \<Gamma> exp1 type \<Longrightarrow> bexp_wt \<Gamma> exp2 type \<Longrightarrow> bexp_wt \<Gamma> (Bxnor exp1 exp2) type"
| "bexp_wt \<Gamma> (Bsig sig) (Lty ki len) \<Longrightarrow> res = l - r + 1 \<Longrightarrow> r \<le> l \<Longrightarrow> res \<le> len \<Longrightarrow> l < len
                                                  \<Longrightarrow>  bexp_wt \<Gamma> (Bslice sig l r) (Lty ki res)"
| "bexp_wt \<Gamma> (Bsig sig) (Lty ki len) \<Longrightarrow> idx < len \<Longrightarrow> bexp_wt \<Gamma> (Bindex sig idx) Bty"
| "bexp_wt \<Gamma> exp1 (Lty Uns len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Uns len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Uns (max len1 len2) \<Longrightarrow> bexp_wt \<Gamma> (Badd exp1 exp2)  ty"
| "bexp_wt \<Gamma> exp1 (Lty Sig len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Sig len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Sig (max len1 len2) \<Longrightarrow> bexp_wt \<Gamma> (Badd exp1 exp2)  ty"
| "bexp_wt \<Gamma> exp1 (Lty Uns len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Uns len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Uns (len1 + len2) \<Longrightarrow> bexp_wt \<Gamma> (Bmult exp1 exp2)   ty"
| "bexp_wt \<Gamma> exp1 (Lty Sig len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Sig len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Sig (len1 + len2) \<Longrightarrow> bexp_wt \<Gamma> (Bmult exp1 exp2)   ty"
| "bexp_wt \<Gamma> exp1 (Lty Uns len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Uns len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Uns (max len1 len2) \<Longrightarrow> bexp_wt \<Gamma> (Bsub exp1 exp2)  ty"
| "bexp_wt \<Gamma> exp1 (Lty Sig len1) \<Longrightarrow> bexp_wt \<Gamma> exp2 (Lty Sig len2) \<Longrightarrow> 0 < len1 \<Longrightarrow> 0 < len2 \<Longrightarrow> ty = Lty Sig (max len1 len2) \<Longrightarrow> bexp_wt \<Gamma> (Bsub exp1 exp2)  ty"
| "bexp_wt \<Gamma> exp  (Lty Uns len ) \<Longrightarrow> 0 < len \<Longrightarrow> bexp_wt \<Gamma> (Bshiftl exp n)  (Lty Uns len)"
| "bexp_wt \<Gamma> exp  (Lty Sig len ) \<Longrightarrow> 0 < len \<Longrightarrow> bexp_wt \<Gamma> (Bshiftl exp n)  (Lty Sig len)"
| "bexp_wt \<Gamma> exp  (Lty Uns len ) \<Longrightarrow> 0 < len \<Longrightarrow> bexp_wt \<Gamma> (Bshiftr exp n)  (Lty Uns len)"
| "bexp_wt \<Gamma> exp  (Lty Sig len ) \<Longrightarrow> 0 < len \<Longrightarrow> bexp_wt \<Gamma> (Bshiftr exp n)  (Lty Sig len)"
| "bexp_wt \<Gamma> g Bty \<Longrightarrow> bexp_wt \<Gamma> th ty \<Longrightarrow> bexp_wt \<Gamma> el ty \<Longrightarrow> bexp_wt \<Gamma> (Bwhen th g el) ty"
| "n = length val \<Longrightarrow> ty = Lty sign n \<Longrightarrow> bexp_wt \<Gamma> (Bliteral sign val) ty"

inductive_cases bexp_wt_cases :   "bexp_wt \<Gamma> (Bnot  exp) type"
                                  "bexp_wt \<Gamma> (Band  exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bor   exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bnand exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bnor  exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bxor  exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bxnor exp1 exp2) type" and
             bexp_wt_cases_slice: "bexp_wt \<Gamma> (Bslice sig l r)  type"
                                  "bexp_wt \<Gamma> (Bsig sig) type"
                                  "bexp_wt \<Gamma> (Bindex sig idx) type"
                                  "bexp_wt \<Gamma> (Badd exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bmult exp1 exp2) type"
                                  "bexp_wt \<Gamma> (Bsub exp1 exp2) type" and
            bexp_wt_cases_shiftl: "bexp_wt \<Gamma> (Bshiftl exp n) type" and
            bexp_wt_cases_shiftr: "bexp_wt \<Gamma> (Bshiftr exp n) type" and
              bexp_wt_cases_when: "bexp_wt \<Gamma> (Bwhen th g el) type" and
               bexp_wt_cases_lit: "bexp_wt \<Gamma> (Bliteral sign val) type" and 
               bexp_wt_cases_del: "bexp_wt \<Gamma> (Bsig_delayed sig dly) type" and 
               bexp_wt_cases_add: "bexp_wt \<Gamma> (Badd exp1 exp2) type" and 
              bexp_wt_cases_mult: "bexp_wt \<Gamma> (Bmult exp1 exp2) type" and
               bexp_wt_cases_sub: "bexp_wt \<Gamma> (Bsub exp1 exp2) type"

inductive_cases bexp_wt_cases_all : "bexp_wt \<Gamma> exp type"

inductive seq_wt :: "'s tyenv \<Rightarrow> 's seq_stmt \<Rightarrow> bool" where
  "seq_wt \<Gamma> Bnull"
| "seq_wt \<Gamma> s1 \<Longrightarrow> seq_wt \<Gamma> s2 \<Longrightarrow> seq_wt \<Gamma> (Bcomp s1 s2)"
| "bexp_wt \<Gamma> g Bty \<Longrightarrow> seq_wt \<Gamma> s1 \<Longrightarrow> seq_wt \<Gamma> s2 \<Longrightarrow> seq_wt \<Gamma> (Bguarded g s1 s2)"
| "bexp_wt \<Gamma> exp (\<Gamma> sig) \<Longrightarrow> seq_wt \<Gamma> (Bassign_trans sig exp dly)"
| "bexp_wt \<Gamma> exp (\<Gamma> sig) \<Longrightarrow> seq_wt \<Gamma> (Bassign_inert sig exp dly)"
| "bexp_wt \<Gamma> exp ty \<Longrightarrow> seq_wt \<Gamma> (Bcase exp [])"
| "bexp_wt \<Gamma> exp ty \<Longrightarrow> seq_wt \<Gamma> ss \<Longrightarrow> seq_wt \<Gamma> (Bcase exp ((Others, ss) # choices))"
| "bexp_wt \<Gamma> exp ty \<Longrightarrow> bexp_wt \<Gamma> exp' ty \<Longrightarrow> seq_wt \<Gamma> ss \<Longrightarrow> seq_wt \<Gamma> (Bcase exp choices) \<Longrightarrow>
                                               seq_wt \<Gamma> (Bcase exp ((Explicit exp', ss) # choices))"

inductive_cases seq_wt_cases [elim!]: "seq_wt \<Gamma> Bnull"
                                      "seq_wt \<Gamma> (Bcomp s1 s2)"
                                      "seq_wt \<Gamma> (Bguarded g s1 s2)"
                                      "seq_wt \<Gamma> (Bassign_trans sig exp dly)"
                                      "seq_wt \<Gamma> (Bassign_inert sig exp dly)" and
                  seq_wt_cases_bcase: "seq_wt \<Gamma> (Bcase exp choices)"

inductive conc_wt :: "'s tyenv \<Rightarrow> 's conc_stmt \<Rightarrow> bool" where
  "seq_wt \<Gamma> ss \<Longrightarrow> conc_wt \<Gamma> (process sl : ss)"
| "conc_wt \<Gamma> cs1 \<Longrightarrow> conc_wt \<Gamma> cs2 \<Longrightarrow> conc_wt \<Gamma> (cs1 || cs2)"

inductive_cases conc_wt_cases [elim!] : "conc_wt \<Gamma> (process sl : ss)"
                                        "conc_wt \<Gamma> (cs1 || cs2)"

fun type_of :: "val \<Rightarrow> ty" where
  "type_of (Bv b)  = Bty"
| "type_of (Lv ki bs) = Lty ki (length bs)"

definition styping :: "'s tyenv \<Rightarrow> 's state \<Rightarrow> bool" where
  "styping \<Gamma> \<sigma> \<equiv> (\<forall>s. type_of (\<sigma> s) = \<Gamma> s)"

lemma [elim]:
  assumes "styping \<Gamma> \<sigma>"
  shows "type_of (\<sigma> s) = \<Gamma> s"
  using assms unfolding styping_def by auto

definition ttyping :: "'s tyenv \<Rightarrow> 's trans_raw \<Rightarrow> bool" where
  "ttyping \<Gamma> \<tau> \<equiv> (\<forall>t s. t \<in> keys \<tau> \<and> s \<in> dom (\<tau> t) \<longrightarrow> type_of (the (\<tau> t s)) = \<Gamma> s)"

(* lemma signal_of_inr_post3':
  assumes "now \<le> t" and "t < now + dly"
  assumes "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
  assumes "signal_of (\<sigma> s) \<tau> s now = v \<or> signal_of (\<sigma> s) \<tau> s (now + dly) \<noteq> v"
  assumes "\<forall>t \<in> keys (to_trans_raw_sig \<tau> s). type_of (the (\<tau> t s)) = type_of v"
  shows "signal_of (\<sigma> s) (inr_post_raw' s v (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)" (is "signal_of _ ?inr_post _ _ = _")
  using assms
proof (induction v)
  case (Bv x)
  show ?case 
    using signal_of_inr_post3[OF Bv(1-3), of "id"] Bv(4)
    unfolding inr_post_raw_def inr_post_raw'_def purge_raw'_def by auto
next
  case (Lv sign bs)
  then show ?case 
  proof (intro signal_of_def)
    fix n 
    assume "now \<le> t" and "t < now + dly" and "\<And>n. n \<le> now \<Longrightarrow> \<tau> n = 0"
    assume "signal_of (\<sigma> s) \<tau> s now = Lv sign bs \<or> post_necessary_raw dly \<tau> now s (Lv sign bs) (\<sigma> s)"
    assume "n \<le> t"
    have *: "inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly n s = trans_post_raw s (Lv sign bs) (\<sigma> s) (purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs)) now dly n s"
      unfolding inr_post_raw'_def by auto
    have **: "purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs) = combine_trans_bit \<tau>
          (zip (map (\<lambda>n. Bv (lval_of (\<sigma> s) ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit \<tau> n s) now dly s (Bv (lval_of (\<sigma> s) ! n)) (Bv (bs ! n))) [0..<length bs])) sign s
          now dly"
      unfolding purge_raw'_def by auto
    have  "inr_post_raw' s (Lv sign bs) (\<sigma> s) \<tau> now dly n s = purge_raw' \<tau> now dly s (\<sigma> s) (Lv sign bs) n s"
      unfolding * using `n \<le> t` `now \<le> t` `t < now + dly` unfolding trans_post_raw_def post_raw_def preempt_raw_def 
      by auto
    also have "... = 0"
    proof (cases "n \<le> now")
      case True
      then show ?thesis 
        unfolding **  combine_trans_bit_def Let_def using Lv(3) by (auto simp add: zero_fun_def)
    next
      case False
      let ?kset = "
           fold (\<union>)
            (map (keys \<circ> (\<lambda>\<tau>. to_trans_raw_sig \<tau> s) \<circ> snd)
              (zip (map (\<lambda>n. Bv (lval_of (\<sigma> s) ! n)) [0..<length bs]) (map (\<lambda>n. purge_raw (to_trans_raw_bit \<tau> n s) now dly s (Bv (lval_of (\<sigma> s) ! n)) (Bv (bs ! n))) [0..<length bs])))
            {}"
      have "n \<in> ?kset \<or> n \<notin> ?kset"
        by auto
      moreover
      { assume "n \<notin> ?kset"
        hence ?thesis
          using False `n \<le> t` `t < now + dly` unfolding ** combine_trans_bit_def Let_def by (auto simp add: zero_option_def) }
      moreover
      { assume "n \<in> ?kset"
        have  "n \<in> fold (\<union>) (map keys
               (map (\<lambda>\<tau>. to_trans_raw_sig \<tau> s)
                 (map (\<lambda>n. purge_raw (to_trans_raw_bit \<tau> n s) now dly s (Bv (lval_of (\<sigma> s) ! n)) (Bv (bs ! n)))
                   [0..<length bs]))) {}"
          using `n \<in> ?kset` unfolding map_map[THEN sym] map_snd_zip_take  length_map min.idem length_upt
          take_all by auto
        hence helper2:" n \<in> fold (\<union>)
           (map (\<lambda>x. keys
                  (to_trans_raw_sig
                    (purge_raw (to_trans_raw_bit \<tau> x s) now dly s (Bv (lval_of (\<sigma> s) ! x)) (Bv (bs ! x))) s))
         [0..<length bs]) {}" 
          unfolding map_map comp_def  by auto   
        obtain b2 where "b2 \<in> set [0..< length bs]" and "n \<in> keys (to_trans_raw_sig
                        (purge_raw (to_trans_raw_bit \<tau> b2 s) now dly s (Bv (lval_of (\<sigma> s) ! b2)) (Bv (bs ! b2))) s)"
          using member_fold_union[OF helper2] by auto
        hence purge_neq: "purge_raw (to_trans_raw_bit \<tau> b2 s) now dly s (Bv (lval_of (\<sigma> s) ! b2)) (Bv (bs ! b2)) n s \<noteq> 0"
          unfolding keys_def to_trans_raw_sig_def by auto
        { assume "signal_of (\<sigma> s) \<tau> s now = Lv sign bs"
          hence "\<sigma> s = Lv sign bs"
            using signal_of_def Lv(3)  by (metis zero_fun_def)
          have "signal_of (Bv (bs ! b2)) (to_trans_raw_bit \<tau> b2 s) s now = Bv (bs ! b2)"
            apply (rule signal_of_def)
            using Lv(3) unfolding to_trans_raw_bit_def by (auto simp add: zero_fun_def zero_option_def)
          hence "signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s now = Bv (bs ! b2)"
            by (simp add: \<open>\<sigma> s = Lv sign bs\<close>)
          hence False
            using purge_neq False `n \<le> t` `t < now + dly` unfolding purge_raw_def Let_def 
            by (auto simp add: zero_option_def)
          hence ?thesis
            by auto }
        moreover
        { assume "signal_of (\<sigma> s) \<tau> s (now + dly) \<noteq> Lv sign bs"
          hence "(\<exists>i val'. i \<le> now + dly \<and> \<tau> i s = Some val' \<and> val' \<noteq> Lv sign bs \<and> (\<forall>j>i. j \<le> now + dly \<longrightarrow> \<tau> j s = None)) 
              \<or> (\<forall>i\<le>now + dly. \<tau> i s = None) \<and> Lv sign bs \<noteq> \<sigma> s"
            unfolding post_necessary_raw_correctness2 by auto
          moreover
          { assume "(\<exists>i val'. i \<le> now + dly \<and> \<tau> i s = Some val' \<and> val' \<noteq> Lv sign bs \<and> (\<forall>j>i. j \<le> now + dly \<longrightarrow> \<tau> j s = None))"
            then obtain i val' where "i \<le> now + dly" and "\<tau> i s = Some val'" and "val' \<noteq> Lv sign bs" and " (\<forall>j>i. j \<le> now + dly \<longrightarrow> \<tau> j s = None)"
              by auto
            hence "type_of val' = Lty sign (length bs)"
              using Lv(5) unfolding to_trans_raw_sig_def keys_def zero_option_def by auto
            then obtain bs' where "val' = Lv sign bs'" and "length bs' = length bs"
              by (metis ty.distinct(1) ty.inject type_of.elims)
            have "bs \<noteq> bs'"
              using \<open>val' = Lv sign bs'\<close> \<open>val' \<noteq> Lv sign bs\<close> by auto
            have "inf_time (to_trans_raw_sig (to_trans_raw_bit \<tau> b2 s)) s (now + dly) = Some i"
            proof (rule inf_time_someI)
              show "i \<in> dom (to_trans_raw_sig (to_trans_raw_bit \<tau> b2 s) s)"
                using `\<tau> i s = Some val'` `val' = Lv sign bs'`
                unfolding to_trans_raw_bit_def to_trans_raw_sig_def dom_def by (auto split: val.splits)
            next
              show "i \<le> now + dly"
                using `i \<le> now + dly` by auto
            next
              show "\<forall>t\<in>dom (to_trans_raw_sig (to_trans_raw_bit \<tau> b2 s) s). t \<le> now + dly \<longrightarrow> t \<le> i"
                by (metis (lifting) \<open>\<forall>j>i. j \<le> now + dly \<longrightarrow> \<tau> j s = None\<close> domIff leI option.simps(4) to_trans_raw_bit_def to_trans_raw_sig_def)
            qed
            moreover have "the (to_trans_raw_sig (to_trans_raw_bit \<tau> b2 s) s i) = Bv (bs' ! b2)"
              using `\<tau> i s = Some val'` `val' = Lv sign bs'` unfolding to_trans_raw_bit_def to_trans_raw_sig_def by auto
            ultimately have "signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s (now + dly) = Bv (bs' ! b2)"
              unfolding to_signal_def comp_def by auto
            have "bs ! b2 \<noteq> bs' ! b2 \<or> bs ! b2 = bs' ! b2"
              by auto
            moreover
            { assume "bs ! b2 \<noteq> bs' ! b2"
              hence "signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s (now + dly) \<noteq> Bv (bs ! b2)"
                using \<open>signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s (now + dly) = Bv (bs' ! b2)\<close> by auto
              hence False
                using purge_neq False `n \<le> t` `t < now + dly` unfolding purge_raw_def Let_def 
                by (auto simp add: zero_option_def)
              hence ?thesis
                by auto }
            moreover
            { assume "bs ! b2 = bs' ! b2"
              hence "signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s (now + dly)  Bv (bs ! b2)"
                using \<open>signal_of (Bv (lval_of (\<sigma> s) ! b2)) (to_trans_raw_bit \<tau> b2 s) s (now + dly) = Bv (bs' ! b2)\<close> by auto
              hence False
                using purge_neq False `n \<le> t` `t < now + dly` unfolding purge_raw_def Let_def 
                by (auto simp add: zero_option_def)
            
            }
            
            
            
            }





          }


          hence "post_necessary_raw dly (to_trans_raw_bit \<tau> b2 s) now s (Bv (bs ! b2)) (Bv (lval_of (\<sigma> s) ! b2))"
            unfolding post_necessary_raw_correctness2
          hence False
            using purge_neq False unfolding purge_raw_def Let_def
    

        
        }
          





      }
      show ?thesis 
        unfolding ** combine_trans_bit_def
    qed

  qed
qed *)

lemma ttyping_rem_curr_trans:
  assumes "ttyping \<Gamma> \<tau>"
  shows "ttyping \<Gamma> (\<tau>(t := 0))"
  using assms unfolding ttyping_def
  by (simp add: keys_def)

lemma [elim]:
  assumes "ttyping \<Gamma> \<tau>"
  assumes "inf_time (to_trans_raw_sig \<tau>) sig t = Some a"
  shows "type_of (the (\<tau> a sig)) = \<Gamma> sig"
proof -
  have "a \<in> keys \<tau>"
    using inf_time_some_exists[OF assms(2)]
    by (metis dom_def dom_imp_keys keys_def zero_option_def)
  moreover have "sig \<in> dom (\<tau> a)"
    using inf_time_some_exists[OF assms(2)] unfolding to_trans_raw_sig_def
    by (simp add: dom_def keys_def zero_option_def)
  ultimately show ?thesis
    using assms(1) unfolding ttyping_def by auto
qed

lemma signal_of_preserve_well_typedness:
  fixes t sig
  assumes "ttyping \<Gamma> \<theta>"
  assumes "styping \<Gamma> def"
  defines "v \<equiv> signal_of (def sig) \<theta> sig t"
  shows   "type_of v = \<Gamma> sig"
proof (cases "inf_time (to_trans_raw_sig \<theta>) sig t")
  case None
  hence "v = def sig"
    unfolding v_def to_signal_def comp_def by auto
  hence "type_of v = type_of (def sig)"
    by auto
  also have "... = \<Gamma> sig"
    using assms(2) by auto
  finally show ?thesis
    by auto
next
  case (Some a)
  hence *: "v = the (to_trans_raw_sig \<theta> sig a)" (is "_ = ?rhs")
    unfolding v_def to_signal_def comp_def by auto
  hence "type_of v = type_of ?rhs"
    by auto
  also have "... = type_of (the (\<theta> a sig))"
    unfolding to_trans_raw_sig_def by auto
  also have "... = \<Gamma> sig"
    using assms(1) Some by auto
  finally have "type_of v = \<Gamma> sig"
    by auto
  then show ?thesis
    by auto
qed

lemma beval_raw_preserve_well_typedness:
  assumes "bexp_wt \<Gamma> exp type" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v"
  shows "type_of v = type"
  using assms
proof (induction arbitrary: v rule:bexp_wt.inducts)
  case (19 \<Gamma> exp1 len1 exp2 len2 ty)   
  obtain v1 v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    using beval_cases(17) "19.prems"(4) by blast
  hence "type_of v1 = Lty Uns len1" and "type_of v2 = Lty Uns len2"
    using 19 by auto
  show ?case
    apply (rule beval_cases(17)[OF 19(11)])
    using 19 size_bin_to_bl_aux  
    apply (metis add.right_neutral list.size(3) ty.inject type_of.simps(2))
    using 19 by (metis signedness.distinct(5) ty.inject type_of.simps(2))
next
  case (20 \<Gamma> exp1 len1 exp2 len2 ty)
  obtain v1 v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    using beval_cases(17)[OF 20(11)] by fastforce+
  hence "type_of v1 = Lty Sig len1" and "type_of v2 = Lty Sig len2"
    using 20 by auto
  show ?case
    apply (rule beval_cases(17)[OF 20(11)])
    using 20 size_bin_to_bl_aux  apply (metis signedness.simps(6) ty.inject type_of.simps(2))
    using 20  by (metis add.right_neutral list.size(3) size_bin_to_bl_aux ty.inject type_of.simps(2))
next
  case (17 \<Gamma> exp1 len1 exp2 len2 ty)
  obtain v1 v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    using beval_cases(16)[OF 17(11)] by fastforce+
  hence "type_of v1 = Lty Uns len1" and "type_of v2 = Lty Uns len2"
    using 17 by auto
  show ?case
    apply(rule beval_cases(16)[OF 17(11)])
    using 17 size_bin_to_bl_aux  apply (metis add.right_neutral list.size(3) ty.inject type_of.simps(2))
    using 17 by fastforce
next
  case (18 \<Gamma> exp1 len1 exp2 len2 ty)
  obtain v1 v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    using beval_cases(16)[OF 18(11)] by fastforce+
  hence "type_of v1 = Lty Sig len1" and "type_of v2 = Lty Sig len2"
    using 18 by auto
  show ?case
    apply(rule beval_cases(16)[OF 18(11)])
    using 18 size_bin_to_bl_aux apply fastforce
    using 18 size_bin_to_bl_aux
    by (metis add.right_neutral list.size(3) ty.inject type_of.simps(2))
next
  case (15 \<Gamma> exp1 len1 exp2 len2 ty)
  then  obtain v1 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "type_of v1 = Lty Uns len1"
    by auto
  then obtain bs1 where "v1 = Lv Uns bs1"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  obtain v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2" and "type_of v2 = Lty Uns len2"
    using 15 by auto
  then obtain bs2 where "v2 = Lv Uns bs2"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  let ?v = "Lv Uns (bin_to_bl (max len1 len2) (bl_to_bin (lval_of v1) + bl_to_bin (lval_of v2)))"
  have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Badd exp1 exp2 \<longrightarrow>\<^sub>b ?v"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2\<close>
          \<open>type_of v1 = Lty Uns len1\<close> \<open>type_of v2 = Lty Uns len2\<close> \<open>v1 = Lv Uns bs1\<close> \<open>v2 = Lv Uns bs2\<close>
    unfolding \<open>v1 = Lv Uns bs1\<close> \<open>v2 = Lv Uns bs2\<close>
    by (intro beval_raw.intros) auto
  hence "?v = v"
    using "15.prems"(4) beval_raw_deterministic by blast
  then show ?case
    using size_bin_to_bl   "15.hyps"(5) by auto 
next
  case (16 \<Gamma> exp1 len1 exp2 len2 ty)
  then  obtain v1 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "type_of v1 = Lty Sig len1"
    by auto
  then obtain bs1 where "v1 = Lv Sig bs1"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  obtain v2 where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2" and "type_of v2 = Lty Sig len2"
    using 16 by auto
  then obtain bs2 where "v2 = Lv Sig bs2"
    by (metis ty.distinct(1) ty.inject type_of.elims)
  let ?v = "Lv Sig (bin_to_bl (max len1 len2) (sbl_to_bin (lval_of v1) + sbl_to_bin (lval_of v2)))"
  have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Badd exp1 exp2 \<longrightarrow>\<^sub>b ?v"
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2\<close>
          \<open>type_of v1 = Lty Sig len1\<close> \<open>type_of v2 = Lty Sig len2\<close> \<open>v1 = Lv Sig bs1\<close> \<open>v2 = Lv Sig bs2\<close>
    unfolding \<open>v1 = Lv Sig bs1\<close> \<open>v2 = Lv Sig bs2\<close>
    by (intro beval_raw.intros) auto
  hence "?v = v"
    using "16.prems"(4) beval_raw_deterministic by blast
  then show ?case
    using size_bin_to_bl "16.hyps"(5) by auto
next
  case (5 \<Gamma> sig dly)
  then show ?case
    using signal_of_preserve_well_typedness by fastforce
next
  case (13 \<Gamma> sig ki len res l r)
  obtain v' where "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig sig \<longrightarrow>\<^sub>b v'"
    by (meson "13.prems"(4) beval_cases(13))
  hence "type_of v' = Lty ki len"
    using 13 by auto
  hence "length (nths (lval_of v') {len - l - 1 .. len - r - 1}) = card {i. i < length (lval_of v') \<and> i \<in> {len - l - 1..len - r - 1}}"
    unfolding length_nths by auto
  also have "... = card {i. i < len \<and> i \<in> {len - l - 1..len - r - 1}}"
    using \<open>type_of v' = Lty ki len\<close> by (metis  ty.inject ty.simps(3) type_of.elims val.sel(3))
  also have "... = card ({len - l - 1 .. len - r - 1} \<inter> {i. i < len})"
    by (metis Collect_conj_eq Collect_mem_eq Int_commute)
  also have "... = card ({len - l - 1 .. len - r - 1}) - card ({len - l - 1 .. len - r - 1} - {i. i < len})"
    by (metis Diff_Diff_Int Diff_subset card_Diff_subset finite_Diff finite_atLeastAtMost)
  also have "... = card ({len - l - 1 .. len - r - 1}) "
  proof -
    have "{len - l - 1 .. len - r - 1} - {i. i < len} = {}"
      using 13(2-4) le_less_trans by auto
    show ?thesis
      by (metis \<open>{len - l - 1..len - r - 1} - {i. i < len} = {}\<close> card_empty diff_zero)
  qed
  also have "... = l - r + 1"
    using 13(2-4)   using "13.hyps"(5) by auto
  finally have "length (nths (lval_of v') {len - l - 1 .. len - r - 1}) = l - r + 1"
    by auto
  thus ?case
    by (smt "13.hyps"(2) "13.hyps"(3) "13.hyps"(5) "13.prems"(4) Suc_diff_Suc \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bsig sig \<longrightarrow>\<^sub>b v'\<close> \<open>type_of v' = Lty ki len\<close> beval_cases(1) beval_cases(13) diff_Suc_1 le_less_trans ty.inject type_of.simps(2) val.sel(3))
qed (fastforce)+

lemma post_raw_preserve_type_correctness:
  fixes sig x t dly
  assumes "ttyping \<Gamma> \<tau>" and "type_of x = \<Gamma> sig"
  defines "\<tau>' \<equiv> post_raw sig x \<tau> (t + dly)"
  shows   "ttyping \<Gamma> \<tau>'"
  unfolding ttyping_def
proof (rule, rule, rule)
  fix t' s'
  assume "t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')"
  hence *: "t' \<in> keys (to_trans_raw_sig \<tau>' s')"
    by (simp add: dom_def keys_def to_trans_raw_sig_def zero_option_def)
  have "s' = sig \<or> s' \<noteq> sig"
    by auto
  moreover
  { assume "s' = sig"
    with * have "t' \<le> t + dly"
      unfolding to_trans_raw_sig_def \<tau>'_def post_raw_def keys_def zero_option_def
      using not_le_imp_less by fastforce
    hence "t' < t + dly \<or> t' = t + dly"
      by auto
    moreover
    { assume "t' < t + dly"
      hence "t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')"
        using `t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')` unfolding \<tau>'_def post_raw_def keys_def dom_def
        by simp
      have "\<tau>' t' s' = \<tau> t' s'"
        using `t' < t + dly` unfolding \<tau>'_def post_raw_def by auto
      hence "type_of (the (\<tau>' t' s')) = type_of (the (\<tau> t' s'))"
        by auto
      also have "... = \<Gamma> sig"
        using assms(1) `t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')` unfolding `s' = sig` ttyping_def
        by auto
      finally have "type_of (the (\<tau>' t' s')) = \<Gamma> s'"
        using \<open>s' = sig\<close> by blast }
    moreover
    { assume "t' = t + dly"
      hence "\<tau>' t' s' = Some x"
        unfolding `s' = sig` \<tau>'_def post_raw_def by auto
      hence "type_of (the (\<tau>' t' s')) = type_of x"
        by auto
      also have "... = \<Gamma> sig"
        using assms(2) by auto
      finally have "type_of (the (\<tau>' t' s')) = \<Gamma> s'"
        by (simp add: \<open>s' = sig\<close>) }
    ultimately have "type_of (the (\<tau>' t' s')) = \<Gamma> s'"
      by auto }
  moreover
  { assume "s' \<noteq> sig"
    hence "t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')"
      using `t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')` unfolding \<tau>'_def post_raw_def
      by (smt CollectI domIff fun_upd_apply keys_def zero_fun_def zero_option_def)
    have "\<tau>' t' s' = \<tau> t' s'"
      using `s' \<noteq> sig` unfolding \<tau>'_def post_raw_def  by simp
    hence "type_of (the (\<tau>' t' s')) = type_of (the (\<tau> t' s'))"
      by auto
    also have "... = \<Gamma> s'"
      using assms(1) `t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')` unfolding ttyping_def by auto
    finally have "type_of (the (\<tau>' t' s')) = \<Gamma> s'"
      by auto }
  ultimately show "type_of (the (\<tau>' t' s')) = \<Gamma> s'"
    by auto
qed

lemma preempt_raw_preserve_type_correctness:
  fixes sig x t dly
  assumes "ttyping \<Gamma> \<tau>"
  defines "\<tau>' \<equiv> preempt_raw sig \<tau> (t + dly)"
  shows   "ttyping \<Gamma> \<tau>'"
  unfolding ttyping_def
proof (rule, rule, rule)
  fix t' s'
  assume "t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')"
  hence *: "t' \<in> keys (to_trans_raw_sig \<tau>' s')"
    by (simp add: dom_def keys_def to_trans_raw_sig_def zero_option_def)
  have "s' = sig \<or> s' \<noteq> sig"
    by auto
  moreover
  { assume "s' \<noteq> sig"
    hence "t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')"
      by (smt \<open>t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')\<close> \<tau>'_def domIff fun_upd_apply keys_def mem_Collect_eq
      preempt_raw_def zero_fun_def zero_option_def) }
  moreover
  { assume "s' = sig"
    hence "t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')"
      by (metis (no_types, lifting) \<open>t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')\<close> \<tau>'_def domIff fun_upd_apply
      keys_def mem_Collect_eq preempt_raw_def) }
  ultimately have "t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')"
    by auto
  have "\<tau>' t' s' = \<tau> t' s'"
    unfolding \<tau>'_def preempt_raw_def
    by (metis (full_types) \<open>t' \<in> keys \<tau>' \<and> s' \<in> dom (\<tau>' t')\<close> \<tau>'_def domIff fun_upd_other
    fun_upd_same preempt_raw_def)
  hence "type_of (the (\<tau>' t' s')) = type_of (the (\<tau> t' s'))"
    by auto
  also have "... = \<Gamma> s'"
    using `t' \<in> keys \<tau> \<and> s' \<in> dom (\<tau> t')` assms(1) unfolding ttyping_def by auto
  finally show "type_of (the  (\<tau>' t' s')) = \<Gamma> s'"
    by auto
qed

lemma trans_post_preserve_type_correctness:
  fixes dly t \<sigma> def
  assumes "\<Gamma> sig = type_of x"
  assumes "ttyping \<Gamma> \<tau>"
  defines "\<tau>' \<equiv> trans_post_raw sig x def \<tau> t dly"
  shows   "ttyping \<Gamma> \<tau>'"
proof (cases " post_necessary_raw (dly - 1) \<tau> t sig x def ")
  case True
  hence "\<tau>' =  post_raw sig x \<tau> (t + dly)"
    unfolding \<tau>'_def trans_post_raw_def by auto
  then show ?thesis
    by (simp add: assms(1) assms(2) post_raw_preserve_type_correctness)
next
  case False
  then show ?thesis
    by (simp add: \<tau>'_def assms(2) preempt_raw_preserve_type_correctness trans_post_raw_def)
qed

lemma purge_raw_preserve_type_correctness:
  fixes val def dly t
  assumes "\<Gamma> sig = type_of x"
  assumes "ttyping \<Gamma> \<tau>"
  defines "\<tau>' \<equiv> purge_raw \<tau> t dly sig def val"
  shows   "ttyping \<Gamma> \<tau>'"
  using assms
  by (smt domIff fun_upd_eqD fun_upd_triv keys_def mem_Collect_eq override_on_def purge_raw_def
  purge_raw_does_not_affect_other_sig ttyping_def zero_fun_def zero_option_def)

lemma inr_post_preserve_type_correctness:
  fixes dly t \<sigma> def
  assumes "\<Gamma> sig = type_of x"
  assumes "ttyping \<Gamma> \<tau>"
  defines "\<tau>' \<equiv> inr_post_raw sig x def \<tau> t dly"
  shows   "ttyping \<Gamma> \<tau>'"
  using assms
  by (simp add: inr_post_raw_def purge_raw_preserve_type_correctness
  trans_post_preserve_type_correctness)

lemma inr_post_preserve_type_correctness':
  fixes dly t \<sigma> def
  assumes "\<Gamma> sig = type_of x"
  assumes "ttyping \<Gamma> \<tau>"
  defines "\<tau>' \<equiv> inr_post_raw' sig x def \<tau> t dly"
  shows   "ttyping \<Gamma> \<tau>'"
  sorry

lemma beval_raw_progress:
  assumes "bexp_wt \<Gamma> exp type" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  shows "\<exists>v. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v "
  using assms
proof (induction rule:bexp_wt.inducts)
  case (25 \<Gamma> th ty el g)
  then show ?case
    by (metis (full_types) beval_raw.intros(32) beval_raw.intros(33)
    beval_raw_preserve_well_typedness ty.distinct(1) type_of.cases type_of.simps(2))
next
  case (21 \<Gamma> exp len n)
  then show ?case
    by (metis beval_raw.intros(28) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (22 \<Gamma> exp len n)
  then show ?case
    by (metis beval_raw.intros(29) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (23 \<Gamma> exp len n)
  then show ?case
    by (metis beval_raw.intros(30) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (24 \<Gamma> exp len n)
  then show ?case
    by (metis beval_raw.intros(31) beval_raw_preserve_well_typedness
    ty.distinct(1) ty.inject type_of.cases type_of.simps(1) type_of.simps(2))
next
  case (19 \<Gamma> exp1 len1 exp2 len2)
  then show ?case
    by (metis beval_raw.intros(26) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (20 \<Gamma> exp1 len1 exp2 len2)
  then show ?case
    by (metis beval_raw.intros(27) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (17 \<Gamma> exp1 len1 exp2 len2)
  then show ?case
    by (metis beval_raw.intros(24) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (18 \<Gamma> exp1 len1 exp2 len2)
  then show ?case
    by (metis beval_raw.intros(25) beval_raw_preserve_well_typedness ty.distinct(1) ty.inject
    type_of.elims)
next
  case (15 \<Gamma> exp1 len1 exp2 len2)
  then obtain v1 and v2 where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "type_of v1 = Lty Uns len1"
    "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp2 \<longrightarrow>\<^sub>b v2" and "type_of v2 = Lty Uns len2"
    using beval_raw_preserve_well_typedness by blast
  then show ?case
    by (metis beval_raw.intros(22) ty.distinct(1) ty.inject type_of.elims)
next
  case (16 \<Gamma> exp1 len1 exp2 len2)
  then obtain v1 and v2 where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and "type_of v1 = Lty Sig len1"
    "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp2 \<longrightarrow>\<^sub>b v2" and "type_of v2 = Lty Sig len2"
    using beval_raw_preserve_well_typedness by blast
  then show ?case
    by (metis beval_raw.intros(23) ty.distinct(1) ty.inject type_of.elims)
next
  case (14 \<Gamma> sig len idx)
  then show ?case
    by (metis beval_raw.intros(21) beval_raw_preserve_well_typedness ty.simps(3) type_of.elims)
next
  case (6 \<Gamma> exp type)
  then show ?case
    by (metis beval_raw.intros(6) beval_raw.intros(7) type_of.elims)
next
  case (7 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 7 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis "7.IH"(2) "7.hyps"(2) "7.prems"(1) "7.prems"(2) "7.prems"(3) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile>
      exp1 \<longrightarrow>\<^sub>b v1\<close> \<open>type_of v1 = type\<close> beval_raw.intros(8) beval_raw_preserve_well_typedness
      ty.distinct(1) type_of.elims)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct(1) ty.inject type_of.elims)
    then show ?thesis
      by (metis (full_types) beval_raw.intros(9) v1 v2)
  qed
next
  case (8 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 8 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> beval_raw.intros(10) ty.distinct(1)
      type_of.elims v1 v2)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct(1) ty.inject type_of.elims)
    then show ?thesis
      by (metis beval_raw.intros(11) v1 v2)
  qed
next
  case (9 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 9 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> beval_raw.intros(12) ty.distinct(1) type_of.elims v1 v2)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct(1) ty.inject type_of.elims)
    then show ?thesis
      by (metis beval_raw.intros(13) v1 v2)
  qed
next
  case (10 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 10 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> beval_raw.intros(14) ty.distinct(1) type_of.elims v1 v2)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct(1) ty.inject type_of.elims)
    then show ?thesis
      by (metis beval_raw.intros(15) v1 v2)
  qed
next
  case (11 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 11 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> beval_raw.intros ty.distinct type_of.elims v1 v2)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct ty.inject type_of.elims)
    then show ?thesis
      by (metis beval_raw.intros v1 v2)
  qed
next
  case (12 \<Gamma> exp1 type exp2)
  then obtain v1 v2 where v1: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp1 \<longrightarrow>\<^sub>b v1" and v2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> exp2 \<longrightarrow>\<^sub>b v2"
    by auto
  hence "type_of v1 = type" and "type_of v2 = type"
    using beval_raw_preserve_well_typedness 12 by blast+
  then show ?case
  proof (cases type)
    case Bty
    then show ?thesis
      by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> beval_raw.intros ty.distinct type_of.elims v1 v2)
  next
    case (Lty ki len)
    then obtain l1 l2 where "v1 = Lv ki l1" and "v2 = Lv ki l2" and "length l1 = len" and "length l2 = len"
      using v1 v2  by (metis \<open>type_of v1 = type\<close> \<open>type_of v2 = type\<close> ty.distinct ty.inject type_of.elims)
    then show ?thesis
      by (metis beval_raw.intros v1 v2)
  qed
next
  case (13 \<Gamma> sig len r l)
  then show ?case
    by (metis beval_raw.intros(20) beval_raw_preserve_well_typedness ty.simps(3) type_of.elims)
qed (auto intro!: beval_raw.intros)

lemma seq_stmts_preserve_type_correctness:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  shows "ttyping \<Gamma> \<tau>'"
  using assms
proof (induction arbitrary: \<tau> \<tau>' rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by auto
next
  case (2 \<Gamma> s1 s2)
  then show ?case  by (meson seq_cases_bcomp)
next
  case (3 \<Gamma> g s1 s2)
  then show ?case  by (meson seq_cases_bguarded)
next
  case (4 \<Gamma> exp sig dly)
  then obtain x where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x"
    by (meson seq_cases_trans)
  hence "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly"
    using 4 beval_raw_deterministic  by (metis seq_cases_trans)
  then show ?case
    using trans_post_preserve_type_correctness
    by (metis "4.hyps" "4.prems"(1) "4.prems"(2) "4.prems"(3) "4.prems"(4) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp
    \<longrightarrow>\<^sub>b x\<close> beval_raw_preserve_well_typedness)
next
  case (5 \<Gamma> exp sig dly)
  then obtain x where "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x"
    by (meson seq_cases_inert)
  hence "\<tau>' = inr_post_raw' sig x (\<sigma> sig) \<tau> t dly"
    using 5 beval_raw_deterministic by (metis seq_cases_inert)
  then show ?case
    using inr_post_preserve_type_correctness'
    by (metis "5.hyps" "5.prems"(1) "5.prems"(2) "5.prems"(3) "5.prems"(4) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp
    \<longrightarrow>\<^sub>b x\<close> beval_raw_preserve_well_typedness)
next
  case (6 \<Gamma> exp ty)
  hence "\<tau>' = \<tau>"
    using b_seq_exec.intros(10) b_seq_exec_deterministic by metis
  then show ?case
    using \<open>ttyping \<Gamma> \<tau>\<close> by auto
next
  case (7 \<Gamma> exp ty ss choices)
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
    by (smt b_seq_exec.cases choices.distinct(1) list.distinct(1) list.sel(1) prod.inject
    seq_stmt.distinct(29) seq_stmt.inject(5) seq_stmt.simps(15) seq_stmt.simps(23)
    seq_stmt.simps(29) seq_stmt.simps(33))
  then show ?case
    by (metis "7.IH" "7.prems"(1) "7.prems"(2) "7.prems"(3) "7.prems"(4) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss
    , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>)
next
  case (8 \<Gamma> exp ty exp' ss choices)
  obtain x where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x"
    using "8.hyps"(1) "8.prems"(1) "8.prems"(2) "8.prems"(3) beval_raw_progress by metis
  obtain x' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'"
    using 8 beval_raw_progress by metis
  have " x = x' \<or> x \<noteq> x'"
    by auto
  moreover
  { assume "x = x'"
    have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      apply (rule seq_cases_bcase[OF 8(11), rotated])
      by (metis Pair_inject \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close> \<open>x =
      x'\<close> beval_raw_deterministic choices.inject list.inject)blast+
    hence ?case
      by (metis "8.IH"(1) "8.prems"(1) "8.prems"(2) "8.prems"(3) "8.prems"(4) \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile>
      < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'\<close>) }
  moreover
  { assume "x \<noteq> x'"
    have "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <Bcase exp choices, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
      apply (rule seq_cases_bcase[OF 8(11)])
      by (metis Pair_inject \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b x\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp' \<longrightarrow>\<^sub>b x'\<close> \<open>x \<noteq>
      x'\<close> beval_raw_deterministic choices.inject list.inject) auto
    hence ?case
      using "8.IH"(2) "8.prems"(1) "8.prems"(2) "8.prems"(3) "8.prems"(4) by auto }
  ultimately show ?case
    by auto
qed

lemma clean_zip_preserve_type_correctness:
  fixes   \<tau> \<tau>1 \<tau>2 cs1 cs2
  assumes "ttyping \<Gamma> \<tau>" and "ttyping \<Gamma> \<tau>1" and "ttyping \<Gamma> \<tau>2"
  defines "\<tau>' \<equiv> clean_zip_raw \<tau> (\<tau>1, set (signals_from cs1)) (\<tau>2, set (signals_from cs2))"
  shows "ttyping \<Gamma> \<tau>'"
  using assms
  by (smt CollectI clean_zip_raw_def domIff keys_def prod.simps(2) ttyping_def zero_fun_def zero_option_def)

lemma conc_stmt_preserve_type_correctness:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  shows "ttyping \<Gamma> \<tau>'"
  using assms
proof (induction arbitrary: \<tau> \<tau>' rule:conc_wt.inducts)
  case (1 \<Gamma> ss sl)
  then show ?case
    using seq_stmts_preserve_type_correctness by blast
next
  case (2 \<Gamma> cs1 cs2)
  then show ?case
    by (metis clean_zip_preserve_type_correctness conc_cases(2))
qed



lemma bexp_wt_bty_cases:
  assumes "bexp_wt \<Gamma> g type"
  assumes "type = Bty"
  assumes "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def"
  shows "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b (Bv True) \<or> t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b (Bv False)"
  using assms
proof (induction rule:bexp_wt.inducts)
  case (25 \<Gamma> g th ty el)
  then show ?case
    by (metis beval_raw.intros(32) beval_raw.intros(33))
next
  case (14 \<Gamma> sig ki len idx)
  then show ?case
    by (smt beval_raw.intros(1) beval_raw.intros(21) bexp_wt_cases_slice(2) styping_def ty.distinct(1) type_of.simps(1) val.collapse(1) val.collapse(2))
next
  case (1 \<Gamma>)
  then show ?case by (auto intro!: beval_raw.intros)
next
  case (2 \<Gamma>)
  then show ?case by (auto intro!: beval_raw.intros)
next
  case (3 ty \<Gamma> sig)
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig sig \<longrightarrow>\<^sub>b \<sigma> sig"
    by (auto intro!: beval_raw.intros)
  with 3 have "\<sigma> sig = Bv True \<or> \<sigma> sig = Bv False"
    unfolding styping_def  by (metis ty.distinct(1) type_of.elims)
  then show ?case
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bsig sig \<longrightarrow>\<^sub>b \<sigma> sig\<close> by presburger
next
  case (4 \<Gamma> sig)
  then show ?case  by (metis beval_raw.intros(5))
next
  case (5 \<Gamma> sig dly)
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> Bsig_delayed sig dly \<longrightarrow>\<^sub>b signal_of (def sig) \<theta> sig (t - dly)"
    by (meson beval_raw.intros(4))
  moreover have "type_of (signal_of (def sig) \<theta> sig (t - dly)) = Bty"
    using 5 signal_of_preserve_well_typedness  by fastforce
  ultimately have "signal_of (def sig) \<theta> sig (t - dly) = Bv True \<or> signal_of (def sig) \<theta> sig (t - dly) = Bv False"
    by (metis ty.distinct(1) type_of.elims)
  then show ?case
    using \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> Bsig_delayed sig dly \<longrightarrow>\<^sub>b signal_of (def sig) \<theta> sig (t - dly)\<close> by presburger
next
  case (6 \<Gamma> exp type)
  then show ?case  by (metis beval_raw.intros(6) val.inject(1))
next
  case (7 \<Gamma> exp1 type exp2)
  then show ?case  by (metis beval_raw.intros(8) val.inject(1))
next
  case (8 \<Gamma> exp1 type exp2)
  then show ?case  by (metis beval_raw.intros(10) val.inject(1))
next
  case (9 \<Gamma> exp1 type exp2)
  then show ?case  by (metis beval_raw.intros(12) val.inject(1))
next
  case (10 \<Gamma> exp1 type exp2)
  then show ?case by (metis beval_raw.intros(14) val.inject(1))
next
  case (11 \<Gamma> exp1 type exp2)
  then show ?case by (metis beval_raw.intros(16) val.inject(1))
next
  case (12 \<Gamma> exp1 type exp2)
  then show ?case by (metis beval_raw.intros(18) val.inject(1))
qed (blast)+

lemma seq_stmts_progress:
  assumes "seq_wt \<Gamma> ss" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  shows "\<exists>\<tau>'. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  using assms
proof (induction arbitrary: \<tau> rule:seq_wt.inducts)
  case (1 \<Gamma>)
  then show ?case by (auto intro!: b_seq_exec.intros)
next
  case (2 \<Gamma> s1 s2)
  then show ?case
    by (meson b_seq_exec.intros(2) seq_stmts_preserve_type_correctness)
next
  case (3 \<Gamma> g s1 s2)
  hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b (Bv True) \<or> t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> g \<longrightarrow>\<^sub>b (Bv False)"
    using bexp_wt_bty_cases  by blast
  then show ?case
    by (meson "3.IH"(1) "3.IH"(2) "3.prems"(1) "3.prems"(2) "3.prems"(3) "3.prems"(4) b_seq_exec.intros(3) b_seq_exec.intros(4))
next
  case (4 \<Gamma> exp sig dly)
  then show ?case
    by (meson b_seq_exec.intros(5) beval_raw_progress)
next
  case (5 \<Gamma> exp sig dly)
  then show ?case
    by (meson b_seq_exec.intros(6) beval_raw_progress)
next
  case (6 \<Gamma> exp ty)
  then show ?case
    using b_seq_exec.intros(10) by blast
next
  case (7 \<Gamma> exp ty ss choices)
  then show ?case
    by (meson b_seq_exec.intros(9))
next
  case (8 \<Gamma> exp ty exp' ss choices)
  then show ?case
    by (metis b_seq_exec.intros(7) b_seq_exec.intros(8) beval_raw_progress
    only_context_matters_for_progress)
qed

lemma conc_stmts_progress:
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  shows "\<exists>\<tau>'. t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  using assms
proof (induction arbitrary: \<tau> rule:conc_wt.inducts)
  case (1 \<Gamma> ss sl)
  then show ?case
    by (meson b_conc_exec.intros(1) b_conc_exec.intros(2) seq_stmts_progress)
next
  case (2 \<Gamma> cs1 cs2)
  then show ?case by (meson b_conc_exec.intros(3))
qed

thm parallel_comp_assoc

lemma
  "conc_wt \<Gamma> ((cs1 || cs2) || cs3) \<longleftrightarrow> conc_wt \<Gamma> ((cs1 || cs3) || (cs2 || cs3))"
proof 
  assume *: "conc_wt \<Gamma> ((cs1 || cs2) || cs3)"
  hence "conc_wt \<Gamma> cs1" and "conc_wt \<Gamma> cs2" and "conc_wt \<Gamma> cs3"
    by blast+
  hence "conc_wt \<Gamma>(cs1 || cs3)" and "conc_wt \<Gamma> (cs2 || cs3)"
    using conc_wt.intros(2) by blast+
  thus "conc_wt \<Gamma> ((cs1 || cs3) || (cs2 || cs3))"
    by (simp add: conc_wt.intros(2))
next
  assume "conc_wt \<Gamma> ((cs1 || cs3) || cs2 || cs3)"
  hence "conc_wt \<Gamma> cs1" and "conc_wt \<Gamma> cs2" and "conc_wt \<Gamma> cs3"
    by blast+
  thus "conc_wt \<Gamma> ((cs1 || cs2) || cs3)"
    by (simp add: conc_wt.intros(2))
qed  

subsection \<open>Semantics of simulation\<close>

text \<open>The other aspect of the semantics is how to simulate, or in a sense execute, VHDL text. One
has to deal with the advance of simulation time. Rather than advancing time naturally, the
simulation proceeds to the "next interesting point of computation" @{cite "VanTassel1995"}. The
following function does exactly this purpose.\<close>

definition next_time :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> nat" where
  "next_time t \<tau> = (if \<tau> = 0 then t + 1 else LEAST n. dom (\<tau> n) \<noteq> {})"

lemma rem_next_time_almost_all_zero:
  assumes "finite {x. \<tau>' x \<noteq> 0}"
  shows "finite {x. (\<tau>'(Femto_VHDL_raw.next_time t \<tau>' := 0)) x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
  by (metis (mono_tags) upd_eventually_cofinite)

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

definition next_state2 :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal state" where
  "next_state2 t' \<tau>' \<sigma> = (let m = \<tau>' t' in override_on \<sigma> (the o m) (dom m))"

lemma next_state_preserve_styping:
  assumes "styping \<Gamma> \<sigma>"
  assumes "ttyping \<Gamma> \<tau>'"
  shows   "styping \<Gamma> (next_state t \<tau>' \<sigma>)"
  unfolding styping_def
proof
  fix s
  have "s \<in> (dom (\<tau>' (next_time t \<tau>'))) \<or> s \<notin> (dom (\<tau>' (next_time t \<tau>')))"
    by auto
  moreover
  { assume "s \<notin> (dom (\<tau>' (next_time t \<tau>')))"
    hence "next_state t \<tau>' \<sigma> s = \<sigma> s" (is "?lhs = ?rhs")
      unfolding next_state_def Let_def comp_def by auto
    hence "type_of ?lhs = type_of ?rhs"
      by auto
    also have "... = \<Gamma> s"
      using assms(1) unfolding styping_def by auto
    finally have "type_of ?lhs = \<Gamma> s"
      by auto }
  moreover
  { assume "s \<in> (dom (\<tau>' (next_time t \<tau>')))"
    hence "next_state t \<tau>' \<sigma> s = the (\<tau>' (next_time t \<tau>') s)" (is "?lhs = ?rhs")
      unfolding next_state_def Let_def by auto
    hence "type_of ?lhs = type_of ?rhs"
      by auto
    also have "... = \<Gamma> s"
      using assms(2) unfolding ttyping_def
      by (metis (full_types) \<open>s \<in> dom (\<tau>' (next_time t \<tau>'))\<close> domIff dom_imp_keys to_trans_raw_sig_def)
    finally have "type_of ?lhs = \<Gamma> s"
      by auto }
  ultimately show "type_of (next_state t \<tau>' \<sigma> s) = \<Gamma> s"
    by auto
qed

lemma next_state2_preserve_styping:
  assumes "styping \<Gamma> \<sigma>"
  assumes "ttyping \<Gamma> \<tau>'"
  shows   "styping \<Gamma> (next_state2 (t + 1) \<tau>' \<sigma>)"
  unfolding styping_def
proof
  fix s
  have "s \<in> (dom (\<tau>' (t + 1))) \<or> s \<notin> (dom (\<tau>' (t + 1)))"
    by auto
  moreover
  { assume "s \<notin> (dom (\<tau>' (t + 1)))"
    hence "next_state2 (t + 1) \<tau>' \<sigma> s = \<sigma> s" (is "?lhs = ?rhs")
      unfolding next_state2_def Let_def comp_def by auto
    hence "type_of ?lhs = type_of ?rhs"
      by auto
    also have "... = \<Gamma> s"
      using assms(1) unfolding styping_def by auto
    finally have "type_of ?lhs = \<Gamma> s"
      by auto }
  moreover
  { assume "s \<in> (dom (\<tau>' (t + 1)))"
    hence "next_state2 (t + 1) \<tau>' \<sigma> s = the (\<tau>' (t + 1) s)" (is "?lhs = ?rhs")
      unfolding next_state2_def Let_def by auto
    hence "type_of ?lhs = type_of ?rhs"
      by auto
    also have "... = \<Gamma> s"
      using assms(2) unfolding ttyping_def
      by (metis (full_types) \<open>s \<in> dom (\<tau>' (t + 1))\<close> domIff dom_imp_keys to_trans_raw_sig_def)
    finally have "type_of ?lhs = \<Gamma> s"
      by auto }
  ultimately show "type_of (next_state2 (t + 1) \<tau>' \<sigma> s) = \<Gamma> s"
    by auto
qed

lemma [simp]:
  "override_on \<sigma> (the o (0 :: 'a \<rightharpoonup> bool)) (dom (0 :: 'a \<rightharpoonup> bool)) = \<sigma>"
  by (simp add: zero_fun_def zero_option_def)

text \<open>The function @{term "next_event"} checks whether the state at the next interesting point of
computation differs from the current state. Any signal which is different is listed as event.\<close>

definition next_event :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal event" where
  "next_event t \<tau>' \<sigma> = (let m =  \<tau>' (next_time t \<tau>') in {sig. sig \<in> dom m \<and> (the o m) sig \<noteq> \<sigma> sig})"

definition next_event2 :: "nat \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal event" where
  "next_event2 t' \<tau>' \<sigma> = (let m = \<tau>' t' in {sig. sig \<in> dom m \<and> (the o m) sig \<noteq> \<sigma> sig})"

lemma [simp]:
  "{sig. sig \<in> dom (0 :: 'a \<rightharpoonup> bool) \<and> (the o (0 :: 'a \<rightharpoonup> bool)) sig \<noteq> \<sigma> sig} = {}"
  by (simp add:zero_option_def zero_fun_def)

lemma next_event_alt_def:
  "next_event t \<tau>' \<sigma> = {sig. \<sigma> sig \<noteq> next_state t \<tau>' \<sigma> sig}"
  by (smt Collect_cong next_event_def next_state_def override_on_def)

lemma next_event2_alt_def: 
  "next_event2 t' \<tau>' \<sigma> = {sig. \<sigma> sig \<noteq> next_state2 t' \<tau>' \<sigma> sig}"
  by (smt Collect_cong next_event2_def next_state2_def override_on_apply_in override_on_apply_notin)

lemma next_state_fixed_point:
  assumes "sig \<notin> next_event t \<tau>' \<sigma>"
  shows "next_state t \<tau>' \<sigma> sig = \<sigma> sig"
  using assms next_event_alt_def by force

text \<open>After we advance to the next interesting computation point, we need to save the behaviour so
that we can return this as the result in the end of the computation (either when it is quiet or
the maximum simulation time is reached).\<close>

definition add_to_beh :: "'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'signal trans_raw" where
  "add_to_beh \<sigma> \<theta> st fi = (if st < fi then \<theta>(st := Some o \<sigma>) else \<theta>)"

lemma add_to_beh_preserve_type_correctness:
  fixes t t'
  assumes "styping \<Gamma> \<sigma>"
  assumes "ttyping \<Gamma> \<theta>"
  defines "\<theta>' \<equiv> add_to_beh \<sigma> \<theta> t t'"
  shows   "ttyping \<Gamma> \<theta>'"
  using assms
  by (simp add: add_to_beh_def keys_def styping_def ttyping_def)

lemma add_to_beh_almost_all_zero:
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. Femto_VHDL_raw.add_to_beh \<sigma> \<theta> t (Femto_VHDL_raw.next_time t \<tau>') x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite] Femto_VHDL_raw.add_to_beh_def
  by (metis (mono_tags) upd_eventually_cofinite)

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

text \<open>non stuttering\<close>

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

definition add_to_beh2 :: "'signal state \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw" where
  "add_to_beh2 \<sigma> \<theta> st def = (let m = (\<lambda>s. if signal_of (def s) \<theta> s st = \<sigma> s then None else Some (\<sigma> s)) in \<theta>( st := m))"

lemma add_to_beh2_almost_all_zero:
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. Femto_VHDL_raw.add_to_beh2 \<sigma> \<theta> t def x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite] Femto_VHDL_raw.add_to_beh2_def Let_def
  using upd_eventually_cofinite by fastforce

inductive b_simulate_fin :: "nat \<Rightarrow> nat \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<times> 'signal state \<times> 'signal event \<times> 'signal trans_raw \<times> 'signal trans_raw \<Rightarrow> bool"
  ("_, _ , _ , _ , _, _ \<turnstile> <_ , _> \<leadsto> _") where

  \<comment> \<open>Business as usual: not quiesced yet and there is still time --- case 1\<close>
  "    (t < maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')
   \<Longrightarrow> (next_time t \<tau>' \<le> maxtime)
   \<Longrightarrow> (maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh2 \<sigma> \<theta> t def,          
                          def \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res)"


  \<comment> \<open>Business as usual: not quiesced yet and there is still time --- case 2\<close>
| "    (t < maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')
   \<Longrightarrow> (maxtime < next_time t \<tau>')
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, \<tau>'))"

  \<comment> \<open>The simulation has quiesced and there is still time\<close>
| "    (t < maxtime)
   \<Longrightarrow> (quiet \<tau> \<gamma>)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (maxtime, \<sigma>, \<gamma>, \<theta>, 0))"

| "     t = maxtime 
   \<Longrightarrow>  maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> (maxtime, \<sigma>, \<gamma>, \<theta>, \<tau>)"
  
inductive b_simulate_fin_suc :: "nat \<Rightarrow> nat \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<times> 'signal state \<times> 'signal trans_raw \<times> 'signal trans_raw \<Rightarrow> bool"
  ("_, _ , _ , _ , _, _ \<turnstile> <_ , _> \<leadsto>s _") where
  "    (t < maxtime) 
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>') 
   \<Longrightarrow> (maxtime, 
          t + 1, 
            next_state2 (t + 1) \<tau>' \<sigma>, 
              next_event2 (t + 1) \<tau>' \<sigma>, 
                \<theta>(t := Some o \<sigma>), 
                  def \<turnstile> <cs, \<tau>'(t + 1 := 0)> \<leadsto>s res)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res)"

|  "maxtime, maxtime, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s (maxtime, \<sigma>, \<theta>, \<tau>)"

lemma maxtime_lt_fst_tres:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> tres"
  shows   "maxtime = fst tres"
  using assms
  by induction auto

lemma final_time_b_simulate_fin_suc:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res"
  shows   "fst res = maxtime"
  using assms
  by (induction rule:b_simulate_fin_suc.induct)(auto)

lemma final_time_eq:
  assumes "maxtime, t ,\<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  shows "fst res1 = fst res2"
  using assms maxtime_lt_fst_tres final_time_b_simulate_fin_suc by metis

abbreviation get_time  where "get_time  \<equiv> fst"
abbreviation get_state where "get_state \<equiv> fst o snd"
abbreviation get_event where "get_event \<equiv> fst o snd o snd"
abbreviation get_beh   where "get_beh   \<equiv> fst o snd o snd o snd"
abbreviation get_trans where "get_trans \<equiv> snd o snd o snd o snd"

lemma add_to_beh2_eventually_cofinite:
  assumes "\<forall>\<^sub>\<infinity>x. \<theta> x = 0"
  shows   "\<forall>\<^sub>\<infinity>x. add_to_beh2 \<sigma> \<theta> t def x = 0"
  unfolding add_to_beh2_def Let_def
  using assms upd_eventually_cofinite by fastforce

lemma b_simulate_fin_almost_all_zero:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. (get_beh res) x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case
    using 1(6)  using "1.prems" upd_eventually_cofinite 
    unfolding add_to_beh2_def Let_def by force
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case
    by (simp add: add_to_beh2_eventually_cofinite)
next
  case (3 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    by (smt MOST_ge_nat comp_apply eventually_elim2 fst_conv fun_upd_other leD snd_conv)
qed auto

lemma b_simulate_fin_almost_all_zero2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "finite {x. \<tau> x \<noteq> 0}"
  assumes "finite {x. \<theta> x \<noteq> 0}"
  shows "finite {x. (get_trans res) x \<noteq> 0}"
  using assms unfolding sym[OF eventually_cofinite]
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have "\<forall>\<^sub>\<infinity>x. \<tau>' x = 0"
    using b_conc_exec_almost_all_zero \<open>\<forall>\<^sub>\<infinity>x. \<tau> x = 0\<close> \<open>\<forall>\<^sub>\<infinity>x. \<theta> x = 0\<close>
    eventually_cofinite  using "1.hyps"(3) by fastforce
  thus ?case
    using "1.IH"  using "1.prems"(2) upd_eventually_cofinite 
  proof -
    have "\<forall>\<^sub>\<infinity>n. add_to_beh2 \<sigma> \<theta> t def n = 0"
      by (simp add: \<open>\<forall>\<^sub>\<infinity>x. \<theta> x = 0\<close> add_to_beh2_eventually_cofinite)
    then show ?thesis
      using "1.IH" \<open>\<forall>\<^sub>\<infinity>x. \<tau>' x = 0\<close> upd_eventually_cofinite by force
  qed
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence " \<forall>\<^sub>\<infinity>x. \<tau>' x = 0"
    using b_conc_exec_almost_all_zero
  proof -
    have f1: "finite {n. \<theta> n \<noteq> 0}"
      by (simp add: "2.prems"(2) \<open>\<And>P. finite {x. \<not> P x} = Alm_all P\<close>)
    have "finite {n. \<tau> n \<noteq> 0}"
      by (simp add: "2.prems"(1) \<open>\<And>P. finite {x. \<not> P x} = Alm_all P\<close>)
    then show ?thesis
      using f1 "2.hyps"(3) \<open>\<And>P. finite {x. \<not> P x} = Alm_all P\<close> b_conc_exec_almost_all_zero by blast
  qed
  then show ?case
    by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  by (simp add: zero_fun_def)
qed auto

inductive_cases bau: "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
inductive_cases bau_suc: "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s beh"

lemma b_simulate_fin_parallel_commute:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "conc_stmt_wf (cs)"
  assumes "cs = cs1 || cs2"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2 || cs1, \<tau>> \<leadsto> beh"
  using assms
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case 
    using parallel_comp_commute  by (metis b_simulate_fin.intros(1))
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case 
    by (simp add: b_simulate_fin.intros(2) parallel_comp_commute')
qed (auto intro!: b_simulate_fin.intros)

lemma b_simulate_fin_parallel_commute_eq:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2, \<tau>> \<leadsto> beh \<longleftrightarrow> maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs2 || cs1, \<tau>> \<leadsto> beh"
  using assms b_simulate_fin_parallel_commute 
  by (metis conc_stmt_wf_def disjoint_iff_not_equal distinct_append signals_from.simps(2))

lemma b_simulate_fin_parallel_distrib1:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  assumes "cs = (cs1 || cs3) || (cs2 || cs3)"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<leadsto> beh"
  using assms
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <(cs1 || cs2) || cs3 , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res"
    by blast
  have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(cs1 || cs2) || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_composition_distrib[OF 1(7)] 1(3) unfolding 1(8) by auto
  then show ?case 
    by (meson "1.IH" "1.hyps"(1) "1.hyps"(2) "1.hyps"(4) "1.prems"(2) assms(2) b_simulate_fin.intros(1))
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  have "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(cs1 || cs2) || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_composition_distrib[OF 2(5)] 2(3) unfolding 2(6) by auto
  then show ?case 
    by (simp add: "2.hyps"(1) "2.hyps"(2) "2.hyps"(4) b_simulate_fin.intros(2))
qed (auto intro!: b_simulate_fin.intros)

lemma b_simulate_fin_parallel_distrib2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "conc_stmt_wf cs"
  assumes "cs = (cs1 || cs2) || cs3"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs3) || (cs2 || cs3), \<tau>> \<leadsto> beh"
  using assms
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case 
    by (simp add: "1.IH" b_simulate_fin.intros(1) parallel_composition_distrib)
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <(cs1 || cs3) || (cs2 || cs3) , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (simp add: parallel_composition_distrib)
  then show ?case 
    by (simp add: "2.hyps"(1) "2.hyps"(2) "2.hyps"(4) b_simulate_fin.intros(2))
qed (auto intro!: b_simulate_fin.intros)


lemma b_simulat_fin_parallel_distrib:
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs3) || (cs2 || cs3), \<tau>> \<leadsto> beh \<longleftrightarrow> 
           maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<leadsto> beh"
  using b_simulate_fin_parallel_distrib1 b_simulate_fin_parallel_distrib2 assms by metis

lemma b_simulate_fin_parallel_assoc1:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  assumes "cs = (cs1 || cs2) || cs3"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2 || cs3, \<tau>> \<leadsto> beh"
  using assms
proof (induction rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2 || cs3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_assoc  by (simp add: parallel_comp_assoc)
  then show ?case 
    using 1  by (meson b_simulate_fin.intros(1))
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs1 || cs2 || cs3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using parallel_comp_assoc  by (simp add: parallel_comp_assoc)
  then show ?case 
    using 2  by (simp add: b_simulate_fin.intros(2))
qed (auto intro!: b_simulate_fin.intros)

lemma b_simulate_fin_parallel_assoc2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  assumes "cs = cs1 || cs2 || cs3"
  shows   "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<leadsto> beh"
  using assms
proof (induction rule: b_simulate_fin.inducts)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (simp add: parallel_comp_assoc2)
  then show ?case 
    using 1  by (meson b_simulate_fin.intros(1))
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  hence "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    by (simp add: parallel_comp_assoc2)
  then show ?case 
    using 2 by (simp add: b_simulate_fin.intros(2))
qed (auto intro!: b_simulate_fin.intros)

lemma b_simulate_fin_parallel_assoc:
  assumes "conc_stmt_wf ((cs1 || cs2) || cs3)"
  shows "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <(cs1 || cs2) || cs3, \<tau>> \<leadsto> beh \<longleftrightarrow> 
         maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < cs1 || cs2 || cs3, \<tau>> \<leadsto> beh"
  using b_simulate_fin_parallel_assoc1 b_simulate_fin_parallel_assoc2 assms by metis

lemma case_quiesce:
  assumes "t < maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "get_beh res = \<theta> \<and> get_state res = \<sigma> \<and> get_trans res = 0"
  apply(rule bau[OF assms(3)])
  using assms by auto

(* lemma case_timesup:
  assumes "\<not> (t \<le> maxtime)"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "get_beh res = \<theta>" and "get_state res = \<sigma>" and "get_trans res = \<tau>"
  using bau[OF assms(2)] assms  by (metis comp_apply fst_conv snd_conv)+
 *)

lemma case_bau:
  assumes "t < maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "next_time t \<tau>' \<le> maxtime"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  shows "(maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh2 \<sigma> \<theta> t def,
                          def \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> beh)"
  using bau[OF assms(5)] assms by (smt b_conc_exec_deterministic nat_neq_iff not_le)

(* lemma case_bau2:
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  obtains \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and
                   "(maxtime,
                       next_time t \<tau>',
                          next_state t \<tau>' \<sigma>,
                              next_event t \<tau>' \<sigma>,
                                  add_to_beh \<sigma> \<theta> t (next_time t \<tau>'),
                                    def \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> beh)"
  using bau[OF assms(3)] assms  *)

lemma beh_res:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "t \<le> maxtime"
  shows "\<And>n. n < t \<Longrightarrow>  \<theta> n =  (get_beh beh) n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal[OF 1(3) 1(8)] by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  hence ind1: "n < next_time t \<tau>'"
    using `n < t` by auto
  have ind2: "(\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0) "
    by (metis next_time_at_least2 rem_curr_trans_preserve_trans_removal)
  hence "add_to_beh2 \<sigma> \<theta> t def n = get_beh res n" using `n < t`
    using "1.IH" "1.hyps"(4) ind1 by auto
  thus ?case
    using `n < t`
    unfolding add_to_beh2_def by auto
qed(auto simp add: add_to_beh2_def)

lemma borderline_big_step:
  fixes \<tau>' :: "'a trans_raw"
  assumes "maxtime, t', \<sigma>', \<gamma>', \<theta>', def' \<turnstile> <cs, \<tau>'(t':=0)> \<leadsto> beh"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t \<le> maxtime" and "maxtime = t'"
  assumes "\<And>n. t < n \<Longrightarrow> \<theta> n = 0"
  assumes "\<theta>' = \<theta>(t:=Some o \<sigma>)"
  shows "\<And>n. n \<le> t' \<Longrightarrow> \<theta>' n = get_beh beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  then show ?case by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma beh_and_res_same_until_now:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>i. i < t \<Longrightarrow> i \<le> maxtime \<Longrightarrow>  \<theta> i = get_beh res i"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have "i < next_time t \<tau>"
    using `i < t` next_time_at_least[OF 1(9), of "t"] "1.prems"(3) less_le_trans next_time_at_least
    by blast
  moreover have "i \<le> maxtime"
    using `i < t` `t < maxtime` by auto
  moreover have "\<And>n. n < next_time t \<tau>' \<Longrightarrow>  (\<tau>'(next_time t \<tau>' := 0)) n = 0"
  proof -
    fix n
    assume "n < next_time t \<tau>'"
    hence "n < t \<or> t \<le> n \<and> n < next_time t \<tau>'"
      by auto
    moreover
    { assume "n < t"
      hence " \<tau>' n = 0"
        using b_conc_exec_preserve_trans_removal[OF 1(3) 1(9), of "t"]
        \<open>n < next_time t \<tau>'\<close> next_time_at_least2 by blast }
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
  ultimately have IH: "(add_to_beh2 \<sigma> \<theta> t def) i =  get_beh res i"
    using 1(5)
    by (smt "1.hyps"(1) "1.hyps"(2) "1.hyps"(3) "1.hyps"(4) "1.prems"(1) "1.prems"(3) add_to_beh2_def b_simulate_fin.intros(1) beh_res fun_upd_apply less_imp_le_nat nat_neq_iff)
  have "t < next_time t \<tau>' \<or> \<not> t < next_time t \<tau>'"
    by auto
  moreover
  { assume "t < next_time t \<tau>'"
    hence ?case
      using IH `i < t` by (auto simp add: add_to_beh2_def) }
  moreover
  { assume "\<not> t < next_time t \<tau>'"
    hence ?case
      using IH `i < t` by (auto simp add: add_to_beh2_def) }
  ultimately show ?case by auto
qed (auto simp add: add_to_beh2_def)

lemma b_conc_exec_does_not_modify_signals2:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "s \<notin> set (signals_from cs)"
  shows   "\<And>i. next_time t \<tau>' \<le> i \<Longrightarrow> signal_of (\<sigma> s) \<tau> s i = signal_of (next_state t \<tau>' \<sigma> s) \<tau>' s i"
proof -
  have *: "\<And>i. \<tau> i s =  \<tau>' i s"
    using b_conc_exec_modifies_local'[OF assms(2) assms(1) assms(3)] by auto
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

definition context_invariant :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal state \<Rightarrow> 'signal trans_raw  \<Rightarrow> bool" where
  "context_invariant t \<sigma> \<gamma> \<theta> def \<tau> \<equiv> (\<forall>n. n < t \<longrightarrow>  \<tau> n = 0)
                                   \<and> (\<gamma> = {s. \<sigma> s \<noteq> signal_of (def s) \<theta> s t})
                                   \<and> (\<forall>n. t < n \<longrightarrow>  \<theta> n = 0)"

lemma context_invariant_rem_curr_trans:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" shows "context_invariant t \<sigma> \<gamma> \<theta> def (\<tau>(t:=0))"
  using assms unfolding context_invariant_def rem_curr_trans_def
  by (simp add: domIff)

lemma nonneg_delay_seq_next_time_strict_bcase:
  assumes "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "ss = Bcase exp choices"
  assumes "nonneg_delay ss"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "(LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
  using assms
proof (induction arbitrary: exp choices rule: b_seq_exec.inducts)
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec.intros(7) b_seq_exec_preserve_trans_removal_nonstrict)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (8 t \<sigma> \<gamma> \<theta> def expa x exp' x' choicesa \<tau> \<tau>' ss)
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec.intros(8) b_seq_exec_preserve_trans_removal_nonstrict)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp' choices')
  hence "\<And>n. n \<le> t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec.intros(9) b_seq_exec_preserve_trans_removal_nonstrict)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  thus ?case
    unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
qed (auto)

lemma nonneg_delay_seq_next_time_bcase:
  assumes "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "ss = Bcase exp choices"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
  using assms
proof (induction arbitrary: exp choices rule: b_seq_exec.inducts)
  case (7 t \<sigma> \<gamma> \<theta> def exp x exp' ss \<tau> \<tau>' choices)
  hence "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec_preserve_trans_removal dual_order.strict_implies_order)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (8 t \<sigma> \<gamma> \<theta> def expa x exp' x' choicesa \<tau> \<tau>' ss)
  hence "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec_preserve_trans_removal less_or_eq_imp_le)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (9 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' exp' choices')
  hence "\<And>n. n < t \<Longrightarrow> \<tau>' n = 0"
    by (meson b_seq_exec_preserve_trans_removal le_eq_less_or_eq)
  then show ?case
    using \<open>\<tau>' \<noteq> 0\<close> unfolding zero_fun_def zero_option_def
    by (meson LeastI_ex dom_eq_empty_conv le_less_linear)
next
  case (10 t \<sigma> \<gamma> \<theta> def exp \<tau>)
  thus ?case
    unfolding zero_fun_def zero_option_def
  proof -
    assume a1: "\<tau> \<noteq> (\<lambda>a. Map.empty)"
    assume a2: "\<And>n. n < t \<Longrightarrow> \<tau> n = Map.empty"
    obtain aa :: "('a \<Rightarrow> val option) \<Rightarrow> 'a" where
      f3: "\<And>f a fa. (dom f \<noteq> {} \<or> f (a::'a) = (None::val option)) \<and> (fa (aa fa) \<noteq> None \<or> dom fa = {})"
      by (metis (no_types) dom_eq_empty_conv)
    then obtain nn :: nat where
      "dom (\<tau> nn) \<noteq> {}"
      using a1 by meson
    then show ?thesis
      using f3 a2 by (meson LeastI_ex dual_order.asym le_less_linear)
  qed
qed (auto)

lemma nonneg_delay_seq_next_time_strict:
  assumes "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "(LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcase x1 x2)
  then show ?case
    using nonneg_delay_seq_next_time_strict_bcase  by (metis (mono_tags))
next
  case (Bcomp ss1 ss2)
  obtain \<tau>'' where \<tau>''_def: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>''"
    using Bcomp.prems(1) by (metis seq_cases_bcomp)
  have \<tau>'_def: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss2 \<tau>'' \<tau>'"
    using \<tau>''_def Bcomp(3) b_seq_exec_deterministic by (metis seq_cases_bcomp)
  have "\<And>n. n \<le> t \<Longrightarrow>  \<tau>'' n = 0"
    using Bcomp(5)  \<tau>''_def
    Bcomp.prems(2) b_seq_exec_preserve_trans_removal_nonstrict nonneg_delay.simps(2) by blast
  thus ?case
    using Bcomp(2) `nonneg_delay (Bcomp ss1 ss2)` \<tau>'_def `\<tau>' \<noteq> 0` by auto
next
  case (Bguarded x1 ss1 ss2)
  moreover hence "nonneg_delay ss1" and "nonneg_delay ss2"
    by auto
  ultimately show ?case by (metis seq_cases_bguarded)
next
  case (Bassign_trans sig exp dly)
  hence "0 < dly" by auto
  obtain v where "beval_raw t \<sigma> \<gamma> \<theta> def exp v"
    using Bassign_trans.prems(1)  by (meson seq_cases_trans)
  have \<tau>'_def: "\<tau>' =  trans_post_raw sig v (\<sigma> sig) \<tau> t dly"
    using Bassign_trans \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v\<close> beval_raw_deterministic
    by (metis seq_cases_trans)
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
    have " \<tau>' t =  (trans_post_raw sig (v) (\<sigma> sig) \<tau> t dly) t"
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
  obtain v where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v"
    using Bassign_inert.prems(1) by (metis seq_cases_inert)
  have \<tau>'_def: "\<tau>' = inr_post_raw' sig (v) (\<sigma> sig) \<tau> t dly"
    using Bassign_inert  \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v\<close> beval_raw_deterministic
    by (metis seq_cases_inert)
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
    have " \<tau>' t =  (inr_post_raw' sig (v) (\<sigma> sig) \<tau> t dly) t"
      unfolding \<tau>'_def by auto
    also have "... = 0"
    proof -
      have "inr_post_raw' sig (v) (\<sigma> sig) \<tau> t dly =
            trans_post_raw sig (v) (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) (v)) t dly"
        (is "?lhs = ?rhs") unfolding inr_post_raw'_def by auto
      hence " ?lhs t =  ?rhs t"
        by auto
      also have "... = 0"
        using Bassign_inert(3) `0 < dly` using purge_raw_before_now_unchanged'[of "\<tau>" "t" "dly" "sig" "\<sigma> sig" "v"
        "purge_raw' \<tau> t dly sig (\<sigma> sig) (v)"]
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

lemma nonneg_delay_seq_next_time:
  assumes "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "\<tau>' \<noteq> 0"
  shows "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcase x1 x2)
  then show ?case
    using nonneg_delay_seq_next_time_bcase  by (metis (mono_tags))
next
  case (Bcomp ss1 ss2)
  obtain \<tau>'' where \<tau>''_def: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>''"
    using Bcomp.prems(1) by (metis seq_cases_bcomp)
  have \<tau>'_def: "b_seq_exec t \<sigma> \<gamma> \<theta> def ss2 \<tau>'' \<tau>'"
    using \<tau>''_def Bcomp(3) b_seq_exec_deterministic by (metis seq_cases_bcomp)
  have "\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0"
    using Bcomp(5)  \<tau>''_def
    Bcomp.prems(2) b_seq_exec_preserve_trans_removal by (metis)
  thus ?case
    using Bcomp(2) \<tau>'_def `\<tau>' \<noteq> 0` by auto
next
  case (Bguarded x1 ss1 ss2)
  thus ?case by (metis seq_cases_bguarded)
next
  case (Bassign_trans sig exp dly)
  obtain v where "beval_raw t \<sigma> \<gamma> \<theta> def exp v"
    using Bassign_trans.prems(1)  by (meson seq_cases_trans)
  have \<tau>'_def: "\<tau>' =  trans_post_raw sig v (\<sigma> sig) \<tau> t dly"
    using Bassign_trans \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v\<close> beval_raw_deterministic
    by (metis seq_cases_trans)
  hence "\<tau>' \<noteq> 0"
    using Bassign_trans by auto
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_seq_exec_preserve_trans_removal Bassign_trans(3) Bassign_trans(1)
    using Bassign_trans.prems(2) by blast
  show ?case
  proof (rule ccontr)
    assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
    hence **: "(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t"
      by auto
    with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      by (auto simp add: ext zero_fun_def zero_option_def)
    hence "dom (\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {})) \<noteq> {}"
      by (metis (mono_tags, lifting) LeastI_ex)
    moreover have "\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {}) = 0"
      using \<open>\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0\<close> ** by auto
    ultimately show False
      by (simp add: zero_fun_def zero_option_def)
  qed
next
  case (Bassign_inert sig exp dly)
  obtain v where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v"
    using Bassign_inert.prems(1) by (metis seq_cases_inert)
  have \<tau>'_def: "\<tau>' = inr_post_raw' sig (v) (\<sigma> sig) \<tau> t dly"
    using Bassign_inert  \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> exp \<longrightarrow>\<^sub>b v\<close> beval_raw_deterministic
    by (metis seq_cases_inert)
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_seq_exec_preserve_trans_removal Bassign_inert(1) Bassign_inert(3)
    using Bassign_inert.prems(2) by blast
  show ?case
  proof (rule ccontr)
    assume "\<not> t \<le> (LEAST n. dom ( \<tau>' n) \<noteq> {})"
    hence **: "(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t"
      by auto
    with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      by (auto simp add: ext zero_fun_def zero_option_def)
    hence "dom (\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {})) \<noteq> {}"
      by (metis (mono_tags, lifting) LeastI_ex)
    moreover have "\<tau>' (LEAST n. dom (\<tau>' n) \<noteq> {}) = 0"
      using \<open>\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0\<close> ** by auto
    ultimately show False
      by (simp add: zero_fun_def zero_option_def)
  qed
next
  case Bnull
  hence "\<tau>' = \<tau>"
    by auto
  hence 0: "\<And>n. n < t \<Longrightarrow> dom ( \<tau>' n) = {}"
    using Bnull by (simp add: zero_fun_def zero_option_def)
  show ?case
  proof (rule ccontr)
    assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
    hence "(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t"
      by auto
    moreover with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
      unfolding zero_fun_def zero_option_def by auto
    ultimately have "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) \<noteq> {}"
      using LeastI_ex[OF *] by auto
    with 0 show "False"
      using `(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t` by auto
  qed
qed

lemma context_invariant:
  fixes \<tau> :: "'a trans_raw"
  fixes t' :: "nat"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t < next_time t \<tau>'"
  defines "t' \<equiv> next_time t \<tau>'" and "\<sigma>' \<equiv> next_state t \<tau>' \<sigma>" and "\<gamma>' \<equiv> next_event t \<tau>' \<sigma>"
      and "\<theta>' \<equiv> \<theta>(t:=Some o \<sigma>)" and "\<tau>'' \<equiv> \<tau>' (t' := 0)"
  shows "context_invariant t' \<sigma>' \<gamma>' \<theta>' def \<tau>''"
proof -
  have 0: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  hence 1: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
    using assms(3) next_time_at_least2 order.strict_trans1 by blast
  have 2: "\<And>n. t < n \<Longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  have " t \<le> next_time t \<tau>'"
    using assms(3) by auto
  have "\<forall>n. n < t' \<longrightarrow>  \<tau>' n = 0"
    using next_time_at_least2 t'_def by metis
  hence 3:  "\<forall>n. n \<le> t' \<longrightarrow> \<tau>'' n = 0"
    unfolding \<tau>''_def by auto
  have 4: "\<forall>n. t' < n \<longrightarrow>  \<theta>' n = 0"
    unfolding \<theta>'_def add_to_beh_def t'_def using 2 `t \<le> next_time t \<tau>'`
    by auto
  have "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
  proof -
    have "t \<le> t'"
      using assms(3) unfolding t'_def by auto
    have "\<And>n. t < n \<Longrightarrow> n \<le> t' \<Longrightarrow>  \<theta>' n = 0"
      by (auto simp add: \<theta>'_def add_to_beh_def 2 `t < next_time t \<tau>'` t'_def)
    hence "\<And>s. signal_of  (def s) \<theta>' s (t') = signal_of (def s) \<theta>' s t"
      using signal_of_less_ind[OF _ `t \<le> t'`] by metis
    moreover have "\<And>s. signal_of (def s) \<theta>' s t = \<sigma> s"
      using trans_some_signal_of unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'`
      by (metis (full_types) fun_upd_same t'_def)
    finally show "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
      by auto
  qed
  hence "\<gamma>' = {s. \<sigma>' s \<noteq> signal_of (def s) \<theta>' s (t')}"
    unfolding \<gamma>'_def next_event_alt_def \<sigma>'_def by auto
  thus ?thesis
    using 3 4 unfolding \<gamma>'_def t'_def \<theta>'_def \<sigma>'_def context_invariant_def by auto
qed

lemma context_invariant2:
  fixes \<tau> :: "'a trans_raw"
  fixes t' :: "nat"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t \<le> next_time t \<tau>'"
  defines "t' \<equiv> next_time t \<tau>'" and "\<sigma>' \<equiv> next_state t \<tau>' \<sigma>" and "\<gamma>' \<equiv> next_event t \<tau>' \<sigma>"
      and "\<theta>' \<equiv> \<theta>(t:=Some o \<sigma>)" and "\<tau>'' \<equiv> \<tau>' (t' := 0)"
  shows "context_invariant t' \<sigma>' \<gamma>' \<theta>' def \<tau>''"
proof -  
  have 0: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  hence 1: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using assms(3) next_time_at_least2 order.strict_trans1 
    using less_le_trans by fastforce
  have 2: "\<And>n. t < n \<Longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  have " t \<le> next_time t \<tau>'"
    using assms(3) by auto
  have "\<forall>n. n < t' \<longrightarrow>  \<tau>' n = 0"
    using next_time_at_least2 t'_def by metis
  hence 3:  "\<forall>n. n \<le> t' \<longrightarrow> \<tau>'' n = 0"
    unfolding \<tau>''_def by auto
  have 4: "\<forall>n. t' < n \<longrightarrow>  \<theta>' n = 0"
    unfolding \<theta>'_def add_to_beh_def t'_def using 2 `t \<le> next_time t \<tau>'`
    by auto
  have "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
  proof -
    have "t \<le> t'"
      using assms(3) unfolding t'_def by auto
    have "\<And>n. t < n \<Longrightarrow> n \<le> t' \<Longrightarrow>  \<theta>' n = 0"
      by (auto simp add: \<theta>'_def add_to_beh_def 2 `t \<le> next_time t \<tau>'` t'_def)
    hence "\<And>s. signal_of  (def s) \<theta>' s (t') = signal_of (def s) \<theta>' s t"
      using signal_of_less_ind[OF _ `t \<le> t'`] by metis
    moreover have "\<And>s. signal_of (def s) \<theta>' s t = \<sigma> s"
      using trans_some_signal_of unfolding \<theta>'_def add_to_beh_def using `t \<le> next_time t \<tau>'`
      by (metis (full_types) fun_upd_same t'_def)
    finally show "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
      by auto
  qed
  hence "\<gamma>' = {s. \<sigma>' s \<noteq> signal_of (def s) \<theta>' s (t')}"
    unfolding \<gamma>'_def next_event_alt_def \<sigma>'_def by auto
  thus ?thesis
    using 3 4 unfolding \<gamma>'_def t'_def \<theta>'_def \<sigma>'_def context_invariant_def by auto
qed

(* lemma context_invariant_suc:
  fixes \<tau> :: "'a trans_raw"
  fixes t' :: "nat"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs"
  defines "\<sigma>' \<equiv> next_state2 (t + 1) \<tau>' \<sigma>" and "\<gamma>' \<equiv> next_event2 (t + 1) \<tau>' \<sigma>"
      and "\<theta>' \<equiv> \<theta>(t := Some o \<sigma>)" and "\<tau>'' \<equiv> \<tau>' (t + 1 := 0)"
    shows "context_invariant (t + 1) \<sigma>' \<gamma>' \<theta>' def \<tau>''"
proof -               
  have 0: "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  hence 1: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal_nonstrict[OF assms(2)] 
    using assms(3) 
  have 2: "\<And>n. t \<le> n \<Longrightarrow>  \<theta> n = 0"
    using assms unfolding context_invariant_def by auto
  have "\<forall>n. n < (t + 1) \<longrightarrow>  \<tau>' n = 0"
    using "1" by auto  
  hence 3:  "\<forall>n. n \<le> (t + 1) \<longrightarrow> \<tau>'' n = 0"
    unfolding \<tau>''_def by auto
  have 4: "\<forall>n. t + 1 \<le> n \<longrightarrow>  \<theta>' n = 0"
    unfolding \<theta>'_def using 2  by auto
  have "\<And>s. signal_of (def s) \<theta>' s t = \<sigma> s"
    by (metis \<theta>'_def fun_upd_same trans_some_signal_of)
  hence "\<gamma>' = {s. \<sigma>' s \<noteq> signal_of (def s) \<theta>' s t}"
    unfolding \<gamma>'_def next_event2_alt_def \<sigma>'_def by auto 
  thus ?thesis
    using 3 4 unfolding \<gamma>'_def \<theta>'_def \<sigma>'_def context_invariant_def by auto
qed *)

lemma nonneg_delay_conc_next_time_strict:
  assumes "\<And>n. n \<le> t \<Longrightarrow>  \<tau> n = 0"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs"
  assumes "conc_stmt_wf cs" (* this is only to make the proof about parallel composition easier; try to remove this *)
  shows "t < next_time t \<tau>'"
proof (cases "\<tau>' \<noteq> 0")
  case True
  have "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using assms(1) assms(2) b_conc_exec_preserve_trans_removal less_imp_le_nat by blast
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least by auto
  moreover have "(LEAST n. dom ( \<tau>' n) \<noteq> {}) > t"
    using assms True
  proof (induction cs arbitrary: \<tau> \<tau>')
    case (Bpar cs1 cs2)
    obtain \<tau>'' where \<tau>''_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>''"
      using Bpar.prems(2) by blast
    have \<tau>'_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>'' \<tau>'"
      using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)` Bpar(4) \<tau>''_def]
      by auto
    have *: "\<And>n. n \<le> t \<Longrightarrow>  \<tau>'' n = 0"
      using \<tau>''_def Bpar(3)
      Bpar.prems(3) b_conc_exec_preserve_trans_removal_nonstrict nonneg_delay_conc.simps(2) by blast
    show ?case
      using Bpar(2)[OF * `b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>'' \<tau>'`]
        `nonneg_delay_conc (cs1 || cs2)` \<tau>'_def `\<tau>' \<noteq> 0`  `conc_stmt_wf (cs1 || cs2)`
      unfolding conc_stmt_wf_def by simp
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
      hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
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

lemma conc_next_time:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "conc_stmt_wf cs" (* this is only to make the proof about parallel composition easier; try to remove this *)
  shows "t \<le> next_time t \<tau>'"
proof (cases "\<tau>' \<noteq> 0")
  case True
  have h: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using assms(1) assms(2) b_conc_exec_preserve_trans_removal less_imp_le_nat by blast
  hence "t \<le> next_time t \<tau>'"
    using next_time_at_least by auto
  moreover have "(LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
    using assms True
  proof (induction cs arbitrary: \<tau> \<tau>')
    case (Bpar cs1 cs2)
    obtain \<tau>'' where \<tau>''_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>''"
      using Bpar.prems(2) by blast
    have \<tau>'_def: "b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>'' \<tau>'"
      using b_conc_exec_sequential[OF `conc_stmt_wf (cs1 || cs2)` Bpar(4) \<tau>''_def]
      by auto
    have *: "\<And>n. n < t \<Longrightarrow>  \<tau>'' n = 0"
      using \<tau>''_def Bpar(3) Bpar.prems(3)  by (metis b_conc_exec_preserve_trans_removal)
    show ?case
      using Bpar(2)[OF * `b_conc_exec t \<sigma> \<gamma> \<theta> def cs2 \<tau>'' \<tau>'`] \<tau>'_def `\<tau>' \<noteq> 0`  `conc_stmt_wf (cs1 || cs2)`
      unfolding conc_stmt_wf_def by simp
  next
    case (Bsingle sl ss)
    have "disjnt sl \<gamma> \<or> \<not> disjnt sl \<gamma>" by auto
    moreover
    { assume "disjnt sl \<gamma>"
      hence "\<tau>' = \<tau>"
        using Bsingle by auto
      hence 0: "\<And>n. n < t \<Longrightarrow> dom ( \<tau>' n) = {}"
        using Bsingle by (simp add: zero_fun_def zero_option_def)
      have ?case
      proof (rule ccontr)
        assume "\<not> (LEAST n. dom ( \<tau>' n) \<noteq> {}) \<ge> t"
        hence "(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t"
          by auto
        moreover with `\<tau>' \<noteq> 0` have *: "\<exists>n. dom ( \<tau>' n) \<noteq> {}"
          unfolding zero_fun_def zero_option_def by auto
        ultimately have "dom ( \<tau>' (LEAST n. dom ( \<tau>' n) \<noteq> {})) \<noteq> {}"
          using LeastI_ex[OF *] by auto
        with 0 show "False"
          using `(LEAST n. dom ( \<tau>' n) \<noteq> {}) < t` by auto
      qed }
    moreover
    { assume "\<not> disjnt sl \<gamma>"
      hence "t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> < ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
        using Bsingle by auto
      hence ?case
        using Bsingle `\<tau>' \<noteq> 0` using nonneg_delay_seq_next_time by metis }
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
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "conc_stmt_wf cs"
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  shows   "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (\<theta>(t:=Some o \<sigma>)) def (\<tau>'(next_time t \<tau>':=0))"
proof -
  have "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
    using assms(1) unfolding context_invariant_def by auto
  hence "t \<le> next_time t \<tau>'"
    using conc_next_time assms by blast 
  with context_invariant2[OF assms(1-2)] show ?thesis by auto
qed

lemma context_invariant_hist:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows "\<forall>n>next_time t \<tau>'. (\<theta>(t:=Some o \<sigma>)) n = 0"
proof -
  have *: "\<forall>n>t.  \<theta> n = 0" and "\<forall>n<t.  \<tau> n = 0"
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
  assumes "\<forall>n < t.  \<tau> n = 0"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "conc_stmt_wf cs"
  assumes "\<forall>n > t.  \<theta> n = 0"
  assumes "conc_wt \<Gamma> cs" and "styping \<Gamma> \<sigma>" and "ttyping \<Gamma> \<theta>" and "styping \<Gamma> def" and "ttyping \<Gamma> \<tau>"
  shows "next_event t \<tau>' \<sigma> = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s (next_time t \<tau>')} "
proof -
  have "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using assms(1) by auto
  hence 3: "t \<le> next_time t \<tau>'"
    using conc_next_time  assms by blast
  define \<theta>' where \<theta>'_def: "\<theta>' = \<theta>(t:=Some o \<sigma>)"
  define t' where t'_def: "t' = next_time t \<tau>'"
  have "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
  proof -
    have "t \<le> t'"
      using 3 unfolding t'_def by auto
    have "\<And>n. t < n \<Longrightarrow> n \<le> t' \<Longrightarrow>  \<theta>' n = 0"
      by (auto simp add: assms `t \<le> next_time t \<tau>'` t'_def \<theta>'_def)
    hence "\<And>s. signal_of  (def s) \<theta>' s (t') = signal_of (def s) \<theta>' s t"
      using signal_of_less_ind[OF _ `t \<le> t'`] by metis
    moreover have "\<And>s. signal_of (def s) \<theta>' s t = \<sigma> s"
      using trans_some_signal_of unfolding \<theta>'_def add_to_beh_def using `t \<le> next_time t \<tau>'`
      by (metis (full_types) fun_upd_same)
    finally show "\<And>s. signal_of (def s) \<theta>' s (t') = \<sigma> s"
      by auto
  qed
  hence "next_event t \<tau>' \<sigma> = {s. next_state t \<tau>' \<sigma> s \<noteq> signal_of (def s) \<theta>' s (t')}"
    unfolding next_event_alt_def by auto
  thus ?thesis
    unfolding \<theta>'_def t'_def by auto
qed

lemma nonneg_delay_same:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  assumes "nonneg_delay ss"
  shows " \<tau> t =  \<tau>' t"
  using assms
proof (induction rule: b_seq_exec.induct)
  case (1 t \<sigma> \<gamma> \<theta> def \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss1 \<tau> \<tau>'' ss2 \<tau>')
  then show ?case by auto
next
  case (3 t \<sigma> \<gamma> \<theta> def guard ss1 \<tau> \<tau>' ss2)
  then show ?case by auto
next
  case (4 t \<sigma> \<gamma> \<theta> def guard ss2 \<tau> \<tau>' ss1)
  then show ?case by auto
next
  case (5 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence \<tau>'_def: "\<tau>' = trans_post_raw sig x (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence "t < t + dly"
    by auto
  then show ?case
    unfolding \<tau>'_def by (auto simp add: trans_post_raw_def preempt_raw_def post_raw_def)
next
  case (6 t \<sigma> \<gamma> \<theta> def e x sig \<tau> dly \<tau>')
  hence \<tau>'_def: "\<tau>' = inr_post_raw' sig x (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  hence \<tau>'_def': "\<tau>' = trans_post_raw sig x (\<sigma> sig) (purge_raw' \<tau> t dly sig (\<sigma> sig) x) t dly"
    unfolding \<tau>'_def inr_post_raw'_def by auto
  have "t < t + dly"
    using `0 < dly` by auto
  hence " \<tau>' t =  (purge_raw' \<tau> t dly sig (\<sigma> sig) x) t"
    unfolding \<tau>'_def' by (auto simp add: trans_post_raw_def post_raw_def preempt_raw_def)
  also have "... =  \<tau> t"
    using purge_raw_before_now_unchanged' by (metis order_refl)
  finally show " \<tau> t =  \<tau>' t"
    by auto
qed (auto)

text \<open>Again, the context invariant is preserved when we have non-negative delay in the sequential
statement.\<close>

lemma b_seq_exec_preserves_context_invariant:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> < ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  shows "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
proof -
  have "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using assms(1) unfolding context_invariant_def by auto
  hence 0: "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using assms(2) b_seq_exec_preserve_trans_removal by (metis)
  thus ?thesis
    using assms(1) unfolding context_invariant_def by auto
qed

lemma nonneg_delay_conc_same:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "nonneg_delay_conc cs"
  shows " \<tau> t =  \<tau>' t"
  using assms
proof (induction rule:b_conc_exec.inducts)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using nonneg_delay_conc.simps(1) nonneg_delay_same by blast
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "\<tau> t = \<tau>1 t" and "\<tau> t = \<tau>2 t"
    by auto
  then show ?case
    unfolding sym[OF 3(3)] clean_zip_raw_def Let_def by auto
qed

lemma b_conc_exec_preserves_context_invariant:
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows   "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  using assms
proof (induction rule: b_conc_exec.induct)
  case (1 sl \<gamma> t \<sigma> \<theta> def ss \<tau>)
  then show ?case by auto
next
  case (2 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_preserves_context_invariant nonneg_delay_conc.simps(1) by blast
next
  case (3 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>1" and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>2"
    using nonneg_delay_conc.simps by blast+
  have "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using 3 unfolding context_invariant_def by auto
  hence "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal 3
    by (smt b_conc_exec.intros(3) le_less nonneg_delay_conc_same)
  thus ?case
    using 3 unfolding context_invariant_def by auto
qed

lemma init'_preserves_context_invariant:
  assumes "init' t \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>'"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  shows   "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>'"
  using assms
proof (induction rule:init'.inducts)
  case (1 t \<sigma> \<gamma> \<theta> def ss \<tau> \<tau>' sl)
  then show ?case
    using b_seq_exec_preserves_context_invariant nonneg_delay_conc.simps(1) by blast
next
  case (2 t \<sigma> \<gamma> \<theta> def cs1 \<tau> \<tau>1 cs2 \<tau>2 \<tau>')
  hence "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>1" and "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>2"
    using nonneg_delay_conc.simps by blast+
  have "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
    using 2 unfolding context_invariant_def by auto
  hence "\<And>n. n < t \<Longrightarrow>  \<tau>' n = 0"
    using b_conc_exec_preserve_trans_removal 2 init'_preserves_trans_removal_strict
    by (smt clean_zip_raw_preserve_trans_removal)
  then show ?case
    using 2 unfolding context_invariant_def by auto
qed

definition degree :: "'a trans_raw \<Rightarrow> nat" where
  "degree \<tau> = (LEAST n. \<forall>t \<ge>n. \<tau> t = 0)"

lemma
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>" shows "degree \<theta> \<le> t + 1" 
proof -
  have "\<forall>k > t. \<theta> k = 0"
    using assms unfolding context_invariant_def by auto
  thus ?thesis
    unfolding degree_def 
  proof -
    have "\<forall>n. \<not> t + 1 \<le> n \<or> \<theta> n = 0"
      using \<open>\<forall>k>t. \<theta> k = 0\<close> by auto
    then show "(LEAST n. \<forall>na\<ge>n. \<theta> na = 0) \<le> t + 1"
      by (simp add: Least_le)
  qed
qed

text \<open>An important theorem for any inductive definition; the computation should be deterministic.\<close>

theorem b_simulate_fin_deterministic:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res2"
  shows "res2 = res1"
  using assms 
proof (induction arbitrary: res2 rule: b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  then show ?case 
    using "1.IH" "1.hyps"(1) "1.hyps"(2) "1.hyps"(3) "1.hyps"(4) "1.prems" case_bau by blast
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  show ?case 
    apply(rule bau[OF 2(5)])
    using 2 b_conc_exec_deterministic leD by blast+
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case  using bau by blast
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    using bau by blast
qed

lemma add_to_beh2_mono:
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k"
  assumes "\<forall>n. t < n \<longrightarrow>  \<theta> n = 0" and "\<forall>n. t < n \<longrightarrow>  \<theta>2 n = 0"
  shows"\<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (add_to_beh2 \<sigma> \<theta> t def) s k = signal_of (def s) (add_to_beh2 \<sigma> \<theta>2 t def) s k"
  unfolding add_to_beh2_def Let_def
proof (rule)+
  fix s k 
  define m1 where "m1 = (\<lambda>s. if signal_of (def s) \<theta> s t = \<sigma> s then None else Some (\<sigma> s))"
  define m2 where "m2 = (\<lambda>s. if signal_of (def s) \<theta>2 s t = \<sigma> s then None else Some (\<sigma> s))"
  assume "k \<le> next_time t \<tau>'"
  hence "k \<le> t \<or> t < k"
    by linarith
  moreover
  { assume "k \<le> t"
    hence "signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k"        
      using assms(1) by auto
    hence "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
    proof (cases "k = t")
      case True
      obtain val where "m1 s = None \<or> m1 s = Some val"
        using option.exhaust_sel by blast
      moreover
      { assume "m1 s = None"
        hence "signal_of (def s) (\<theta>(t:=m1)) s k = signal_of (def s) (\<theta>(t:=m1)) s (k - 1)"
          using signal_of_less_sig  by (metis True fun_upd_same zero_option_def)
        have "m2 s = None"
          using \<open>m1 s = None\<close> m1_def m2_def 
          using True \<open>signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k\<close> by auto
        have "0 < k \<or> k = 0"
          by auto
        moreover
        { assume "0 < k"
          hence "signal_of (def s) (\<theta>(t:=m1)) s (k - 1) = signal_of (def s) \<theta> s (k - 1)"
            unfolding True 
            by (smt One_nat_def Suc_pred add.right_neutral add_Suc_right comp_def fun_upd_other leD less_add_one order_refl to_signal_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) \<theta>2 s (k - 1)"
            using assms True diff_le_self by blast
          also have "... = signal_of (def s) (\<theta>2(t:=m2)) s (k - 1)"
            using \<open>0 < k\<close> unfolding True 
            by (smt One_nat_def Suc_pred add.right_neutral add_Suc_right fun_upd_other leD le_refl less_add_one signal_of_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
            using signal_of_less_sig   by (metis True \<open>m2 s = None\<close> fun_upd_same zero_option_def)
          finally have " signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
            using \<open>signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t := m1)) s (k - 1)\<close> by auto }
        moreover
        { assume "k = 0"
          hence "signal_of (def s) (\<theta>(t:=m1)) s k = def s"
            unfolding True using `m1 s = None` 
            by (metis fun_upd_same signal_of_zero zero_option_def)
          also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
            unfolding True using `m2 s = None` 
            by (metis True \<open>k = 0\<close> fun_upd_same signal_of_zero zero_option_def)
          finally have " signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
            by auto }
        ultimately have " signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
          by auto }
      moreover
      { assume "m1 s = Some val"
        hence "m2 s = Some val"
          unfolding m1_def m2_def  using True \<open>signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k\<close> by auto
        have " signal_of (def s) (\<theta>(t := m1)) s k = the (m1 s)"
          unfolding True 
          by (metis (mono_tags, hide_lams) \<open>m1 s = Some val\<close> fun_upd_same nat_less_le
              not_less_iff_gr_or_eq option.sel order_refl signal_of_val_eq to_trans_raw_sig_def)
        also have "... = signal_of (def s)(\<theta>2(t:=m2)) s k"
          unfolding True 
          by (metis True \<open>m1 s = None \<Longrightarrow> signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s)
          (\<theta>2(t := m2)) s k\<close> \<open>m1 s = Some val\<close> \<open>m2 s = Some val\<close> calculation fun_upd_same m1_def
          trans_some_signal_of')
        finally have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s)(\<theta>2(t:=m2)) s k"
          by auto }
      ultimately show ?thesis 
        by auto
    next
      case False
      hence "k < t"
        using `k \<le>t ` by auto
      hence "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) \<theta> s k"
        by (metis fun_upd_other not_le order_refl signal_of_equal_when_trans_equal_upto)
      also have "... = signal_of (def s) \<theta>2 s k"
        using \<open>signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k\<close> by blast
      also have "... = signal_of (def s) (\<theta>2(t := m2)) s k"
        using `k < t`
        by (metis fun_upd_other not_le order_refl signal_of_equal_when_trans_equal_upto)
      finally show ?thesis
        by auto            
    qed }
  moreover
  { assume " t < k"
    hence "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t:=m1)) s t"
      using `\<forall>n>t. \<theta> n = 0` 
      by (metis fun_upd_other less_irrefl_nat less_or_eq_imp_le signal_of_less_ind)
    have "0 < k"
      using \<open>t < k\<close> neq0_conv by blast
    have "0 < t \<or> t = 0"
      by auto
    moreover
    { assume "t = 0"
      obtain val where "m1 s = None \<or> m1 s = Some val"
        using option.exhaust_sel by blast
      moreover
      { assume "m1 s = None"
        hence " signal_of (def s) (\<theta>(t:=m1)) s t = def s"
          by (metis \<open>t = 0\<close> fun_upd_same signal_of_zero zero_option_def)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s t"
          by (metis (full_types) assms \<open>m1 s = None\<close> \<open>t = 0\<close> fun_upd_same le0 m1_def m2_def signal_of_zero zero_option_def)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
          using `\<forall>n>t. \<theta>2 n = 0` 
          by (metis \<open>0 < k\<close> \<open>t = 0\<close> fun_upd_other less_imp_le_nat less_imp_not_eq2 signal_of_less_ind)
        finally have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"          
          using \<open>signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t := m1)) s t\<close> by auto }
      moreover
      { assume "m1 s = Some val"
        hence " signal_of (def s) (\<theta>(t:=m1)) s t = val"
          by (metis (mono_tags) \<open>t = 0\<close> fun_upd_same le_zero_eq not_less0 signal_of_intro to_trans_raw_sig_def)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s t"
          by (metis assms \<open>m1 s = Some val\<close> \<open>t = 0\<close> fun_upd_same le0 m1_def m2_def option.distinct(1) option.sel trans_some_signal_of')
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
          using `\<forall>n>t. \<theta>2 n = 0` 
          by (metis \<open>0 < k\<close> \<open>t = 0\<close> fun_upd_other less_not_refl less_or_eq_imp_le signal_of_less_ind)
        finally have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"          
          using \<open>signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t := m1)) s t\<close> by auto }
      ultimately have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
        by auto }
    moreover
    { assume "0 < t"
      obtain val where "m1 s = None \<or> m1 s = Some val"
        using option.exhaust_sel by blast
      moreover
      { assume "m1 s = None"
        hence "signal_of (def s) (\<theta>(t:=m1)) s t = signal_of (def s) (\<theta>(t:=m1)) s (t - 1)"
          using signal_of_less_sig  by (metis fun_upd_same zero_option_def)
        also have  "... = signal_of (def s) \<theta> s (t - 1)"              
          using `0 < t`
          by (metis antisym_conv3 diff_less dual_order.antisym dual_order.refl fun_upd_other less_le less_nat_zero_code less_numeral_extra(1) signal_of_equal_when_trans_equal_upto)
        also have "... = signal_of (def s) \<theta>2 s (t - 1)"
          using assms diff_le_self 
          by (smt assms leI less_imp_le_nat signal_of_less_ind)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s (t - 1)"
          using \<open>0 < t\<close> 
          by (metis (mono_tags, lifting) diff_less fun_upd_other leD o_apply order.refl rel_simps(68) to_signal_equal_when_trans_equal_upto)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s t"
          using signal_of_less_sig 
          by (metis assms \<open>m1 s = None\<close> fun_upd_same m1_def m2_def order_refl zero_option_def)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
          by (metis assms \<open>t < k\<close> dual_order.strict_implies_not_eq dual_order.strict_implies_order fun_upd_other signal_of_less_ind)
        finally have " signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
          using \<open>signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t := m1)) s t\<close> by auto }
      moreover
      { assume "m1 s = Some val"
        hence "signal_of (def s) (\<theta>(t:=m1)) s t = val"
          by (metis (mono_tags, hide_lams) fun_upd_same not_le order_refl signal_of_intro to_trans_raw_sig_def)
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s t"
          by (metis assms \<open>m1 s = Some val\<close> fun_upd_same m1_def m2_def option.distinct(1) option.sel order_refl trans_some_signal_of')
        also have "... = signal_of (def s) (\<theta>2(t:=m2)) s k"
          by (metis assms \<open>t < k\<close> fun_upd_other less_imp_le less_irrefl_nat signal_of_less_ind)
        finally have " signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
          using \<open>signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>(t := m1)) s t\<close> by auto }
      ultimately have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
        by auto }
    ultimately have "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
      by auto }
  ultimately show "signal_of (def s) (\<theta>(t := m1)) s k = signal_of (def s) (\<theta>2(t := m2)) s k"
    by auto
qed

lemma b_simulate_fin_deterministic_weaker:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<leadsto> res2"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<forall>n. t < n \<longrightarrow>  \<theta>1 n = 0" and "\<forall>n. t < n \<longrightarrow>  \<theta>2 n = 0"
  assumes "\<forall>n. n < t \<longrightarrow>  \<tau> n = 0" (* this is annoying *)
  shows   "\<exists>\<sigma>' \<tau>' \<theta>1' \<theta>2' \<gamma>'. res1 = (maxtime, \<sigma>', \<gamma>', \<theta>1', \<tau>') \<and> res2 = (maxtime, \<sigma>', \<gamma>', \<theta>2', \<tau>') \<and> 
          (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) \<theta>1' s k = signal_of (def s) \<theta>2' s k)"
  using assms
proof (induction arbitrary: \<theta>2 res2 rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have *: "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using b_conc_exec_deterministic_weaker[OF 1(3) _ 1(8)]  
          only_context_matters_for_progress_conc_hist[OF 1(3) 1(8)] by blast
  note exec' = 1(7) and IH = 1(6)
  hence **: " maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh2 \<sigma> \<theta>2 t def, def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res2"
    using "1.hyps" * by (meson case_bau)
  have *** : "\<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (add_to_beh2 \<sigma> \<theta> t def) s k = signal_of (def s) (add_to_beh2 \<sigma> \<theta>2 t def) s k"
    using add_to_beh2_mono[OF 1(8-10)] by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least 
    by (metis "*" "1"(11) b_conc_exec_preserve_trans_removal leD nat_le_linear)
  hence four: "\<forall>n>next_time t \<tau>'. (add_to_beh2 \<sigma> \<theta> t def) n = 0" and 
        five: "\<forall>n>next_time t \<tau>'. (add_to_beh2 \<sigma> \<theta>2 t def ) n = 0"
    using 1 unfolding add_to_beh2_def by auto
  have " \<forall>n<next_time t \<tau>'. (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    using `t \<le> next_time t \<tau>'` by (simp add: nat_less_le next_time_at_least2)
  from IH[OF ** *** four five this] show ?case 
    by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  have th: "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using only_context_matters_for_progress_conc_hist[OF 2(3) 2(6)]  b_conc_exec_deterministic_weaker[OF 2(3) _ 2(6)] by blast
  have "res2 = (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta>2 t def, \<tau>')"
    apply (rule bau[OF 2(5)])
    using 2 b_conc_exec_deterministic th 
       apply (metis less_le_not_le)
    using b_conc_exec_deterministic th apply blast
    using "2.hyps"(2) apply blast
    using "2.hyps"(1) by blast
  have *** : "\<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (add_to_beh2 \<sigma> \<theta> t def) s k = signal_of (def s) (add_to_beh2 \<sigma> \<theta>2 t def) s k"
    using add_to_beh2_mono[OF 2(6-8)] by auto
  then show ?case 
    using \<open>res2 = (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta>2 t def, \<tau>')\<close>  using "2.hyps"(4) by auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  have "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>) s k = signal_of (def s) (\<theta>2) s k"
  proof (rule+)
    fix s k
    assume "k \<le> maxtime" hence "k \<le> t \<or> t < k" by linarith
    moreover
    { assume "k \<le> t"
      hence "signal_of (def s) \<theta> s k = signal_of (def s) \<theta>2 s k"        
        using 3 by blast }
    moreover
    { assume " t < k"
      hence "signal_of (def s) (\<theta>) s k = signal_of (def s) (\<theta>2 ) s k"
        using `\<forall>n>t. \<theta>2 n = 0` `\<forall>n>t. \<theta> n = 0` `t < k`
        by (smt "3.prems"(2) less_imp_le_nat pl_pl_rels signal_of_less_ind) }
    ultimately show "signal_of (def s) (\<theta>) s k = signal_of (def s) (\<theta>2) s k"
      by auto
  qed    
  then show ?case 
    using case_quiesce[OF 3(1-3)] 
    by (metis "3.hyps"(1) "3.hyps"(2) "3.prems"(1) b_simulate_fin.intros(3) b_simulate_fin_deterministic) 
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    by (meson b_simulate_fin.intros(4) b_simulate_fin_deterministic)
qed

lemma only_context_matters_b_simulate_fin_progress:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<forall>n. t < n \<longrightarrow>  \<theta>1 n = 0" and "\<forall>n. t < n \<longrightarrow>  \<theta>2 n = 0"
  assumes "\<forall>n. n < t \<longrightarrow>  \<tau> n = 0" (* this is annoying *)
  shows   "\<exists>res2. maxtime, t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<leadsto> res2"
  using assms
proof (induction arbitrary: \<theta>2 rule:b_simulate_fin.inducts)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have *: "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using only_context_matters_for_progress_conc_hist[OF 1(3) 1(7)] b_conc_exec_deterministic_weaker[OF 1(3) _ 1(7)]
    by blast
  have th : "\<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (add_to_beh2 \<sigma> \<theta> t def) s k = signal_of (def s) (add_to_beh2 \<sigma> \<theta>2 t def) s k"
    using add_to_beh2_mono[OF 1(7-9)] by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least  by (metis "*" "1"(10) b_conc_exec_preserve_trans_removal leD nat_le_linear)
  hence four: "\<forall>n>next_time t \<tau>'. (add_to_beh2 \<sigma> \<theta> t def) n = 0" and 
        five: "\<forall>n>next_time t \<tau>'. (add_to_beh2 \<sigma> \<theta>2 t def) n = 0"
    using 1   by (metis (no_types, lifting) add_to_beh2_def dual_order.strict_trans2 fun_upd_other less_irrefl_nat)+
  have " \<forall>n<next_time t \<tau>'. (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    using `t \<le> next_time t \<tau>'` by (simp add: nat_less_le next_time_at_least2)
  hence "\<exists>a. maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh2 \<sigma> \<theta>2 t def, def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> a" 
    using 1(6)[OF th four five] by blast 
  thus ?case
    using b_simulate_fin.intros(1)[OF `t < maxtime` `\<not> quiet \<tau> \<gamma>` * "1.hyps"(4)] by blast 
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  have *: "t , \<sigma> , \<gamma> , \<theta>2, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using only_context_matters_for_progress_conc_hist[OF 2(3) 2(5)] b_conc_exec_deterministic_weaker[OF 2(3) _ 2(5)]
    by blast
  thus ?case 
    using 2 by (intro exI)(auto intro!: b_simulate_fin.intros(2))
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    by (meson b_simulate_fin.intros(3))
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case  by (meson b_simulate_fin.intros(4))
qed

lemma conc_wt_simulation_progress:
  assumes \<open>conc_wt \<Gamma> cs\<close>
  assumes \<open>ttyping \<Gamma> \<tau>\<close> and \<open>ttyping \<Gamma> \<theta>\<close>
  assumes \<open>styping \<Gamma> \<sigma>\<close> and \<open>styping \<Gamma> def\<close>
  assumes \<open>t \<le> maxtime\<close>
  shows   \<open>\<exists>res. maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res\<close>
proof -
  consider "t < maxtime" | "t = maxtime"
    using `t \<le> maxtime` by linarith
  thus ?thesis
  proof (cases)
    case 1
    obtain \<tau>' where "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
      using conc_stmts_progress[OF assms(1) assms(4) assms(3) assms(5) assms(2)]
      by auto
    hence "ttyping \<Gamma> \<tau>'"
      using conc_stmt_preserve_type_correctness[OF assms(1) assms(4) assms(3) assms(5) assms(2)]
      by auto
    thus ?thesis 
      using `t < maxtime` `t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'` assms(4) assms(3) assms(5)
    proof (induction "maxtime - t" arbitrary: t \<sigma> \<gamma> \<theta> def \<tau> \<tau>')
      case 0
      then show ?case  by linarith
    next
      case (Suc x)
      hence "x = maxtime - (t + 1)"
        by auto
      have "t + 1 < maxtime \<or> t + 1 = maxtime"
        using Suc(4) by auto
      moreover
      { assume "t + 1 < maxtime"
        have "styping \<Gamma> (next_state2 (t + 1) \<tau>' \<sigma>)"
          using Suc(3) next_state2_preserve_styping[OF Suc(6) Suc(3)] by auto
        have "ttyping \<Gamma> (\<theta>(t := Some \<circ> \<sigma>))"
          using add_to_beh_preserve_type_correctness[OF Suc(6) Suc(7)]  
          by (metis Suc.prems(2) add_to_beh_def)
        have "ttyping \<Gamma> ( \<tau>'(t + 1 := 0))"
          using ttyping_rem_curr_trans[OF Suc(3)] by auto
        obtain \<tau>'' where "t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta> (t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>'(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>''"
          using conc_stmts_progress[OF assms(1) `styping \<Gamma> (next_state2 (t + 1) \<tau>' \<sigma>)` `ttyping \<Gamma> (\<theta>(t := Some \<circ> \<sigma>))` Suc(8) `ttyping \<Gamma> ( \<tau>'(t + 1 := 0))`]
          by auto
        hence "\<exists>res. b_simulate_fin_suc maxtime (t + 1) (next_state2 (t + 1) \<tau>' \<sigma>) (next_event2 (t + 1) \<tau>' \<sigma>) (\<theta>(t := Some o \<sigma>)) def cs (\<tau>'(t + 1 := 0)) res"
          using Suc(1)[OF `x = maxtime - (t + 1)` `ttyping \<Gamma> ( \<tau>'(t + 1 := 0))` `t + 1 < maxtime` ]
          by (meson Suc.hyps(1) Suc.prems(6) \<open>styping \<Gamma> (next_state2 (t + 1) \<tau>' \<sigma>)\<close> \<open>t + 1 <
          maxtime\<close> \<open>ttyping \<Gamma> (\<tau>'(t + 1 := 0))\<close> \<open>ttyping \<Gamma> (\<theta>(t := Some \<circ> \<sigma>))\<close> \<open>x = maxtime - (t +
          1)\<close> assms(1) conc_stmt_preserve_type_correctness)
        hence ?case
          using b_simulate_fin_suc.intros(1)[OF `t < maxtime` Suc(5)]  by blast }
      moreover
      { assume "t + 1 = maxtime"
        hence "\<exists>res. b_simulate_fin_suc maxtime (t + 1) (next_state2 (t + 1) \<tau>' \<sigma>) (next_event2 (t + 1) \<tau>' \<sigma>) (\<theta>(t := Some o \<sigma>)) def cs (\<tau>'(t + 1 := 0)) res"
          using b_simulate_fin_suc.intros(2) by blast
        hence ?case
          using Suc.prems(2) Suc.prems(3) b_simulate_fin_suc.intros(1) by blast }
      ultimately show ?case 
        by auto
    qed
  next
    case 2
    then show ?thesis 
      using b_simulate_fin_suc.intros(2) by blast
  qed
qed

lemma quiet_fast_forward:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res"
  assumes "quiet \<tau> \<gamma>" and "t < maxtime"
  assumes "\<forall>n\<ge>t. \<theta> n = 0"
  shows   "\<exists>\<theta>'. res = (maxtime, \<sigma>, \<theta>', \<tau>) \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) \<theta>' s k)"
  using assms
proof (induction arbitrary: rule:b_simulate_fin_suc.inducts)
  case (1 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' res)
  hence "\<tau>' = \<tau>"
    using b_conc_exec_empty_event unfolding quiet_def by (metis b_conc_exec_deterministic)
  hence qu: "quiet (\<tau>'(t + 1 := 0)) (next_event2 (t + 1) \<tau>' \<sigma>)"
    using `quiet \<tau> \<gamma>` unfolding quiet_def next_event2_def Let_def comp_def 
    by (metis (mono_tags, lifting) Collect_empty_eq domIff fun_upd_idem_iff zero_fun_def zero_option_def)
  have hi: "\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0"
    using 1  by (metis add_diff_cancel_left' add_leD1 diff_is_0_eq' fun_upd_apply zero_neq_one)
  have "next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>"
    by (metis "1.prems"(1) \<open>\<tau>' = \<tau>\<close> add.commute dom_eq_empty_conv next_state2_def
    override_on_emptyset plus_1_eq_Suc quiet_def zero_fun_def zero_option_def)
  have "\<tau>'(t + 1 := 0) = \<tau>"
    by (metis "1.prems"(1) qu quiet_def)
  consider (less)"t + 1 < maxtime" | (eq)"t + 1 = maxtime"
    using `t < maxtime` by linarith
  then show ?case
  proof (cases)
    case less
    with 1(4)[OF qu less hi] obtain \<theta>'' where "res = (maxtime, \<sigma>, \<theta>'', \<tau>)" and 
      *: "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k)"
      using `next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>` \<open>\<tau>'(t + 1 := 0) = \<tau>\<close> by metis
    have "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k)"
    proof (rule+)
      fix s k
      assume "k \<le> maxtime" consider "k \<le> t" | "k = t + 1" | "t + 1 < k" by linarith
      thus "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k "
      proof (cases)
        case 1
        then show ?thesis using * `t < maxtime` 
          by (smt \<open>k \<le> maxtime\<close> add_le_same_cancel1 comp_apply fun_upd_other leD
          less_numeral_extra(1) to_signal_equal_when_trans_equal_upto)
      next
        case 2
        then show ?thesis 
          using * `t < maxtime` `\<forall>n\<ge>t. \<theta> n = 0`
          by (smt add.commute add_diff_cancel_left' add_le_same_cancel1 discrete fun_upd_same hi
          not_le not_one_le_zero signal_of_less trans_some_signal_of)
      next
        case 3
        then show ?thesis 
          using * `t + 1 < maxtime` `k \<le> maxtime` 
          by (smt "1.hyps"(1) discrete fun_upd_apply hi nat_less_le signal_of_less_ind
          trans_some_signal_of)
      qed
    qed
    thus ?thesis
      using \<open>res = (maxtime, \<sigma>, \<theta>'', \<tau>)\<close> by blast
  next
    case eq
    hence "res = (maxtime, \<sigma>, \<theta>(t := Some o \<sigma>), \<tau>)"
      using 1(3) bau_suc \<open>\<tau>'(t + 1 := 0) = \<tau>\<close> \<open>next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>\<close> by blast
    then show ?thesis by blast
  qed
next
  case (2 maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

lemma not_quiet_fast_forward:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "\<not> quiet \<tau> \<gamma>" and "t < maxtime" and "maxtime < next_time t \<tau>'"
  assumes "\<forall>n\<ge>t. \<theta> n = 0"
  shows   "\<exists>\<theta>'. res = (maxtime, \<sigma>, \<theta>', \<tau>') \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) \<theta>' s k)"
  using assms
proof (induction arbitrary: \<tau>' rule: b_simulate_fin_suc.inducts)
  case (1 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>2 res)
  have hi: " \<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0 "
    using 1(9) by auto
  have "\<tau>2 = \<tau>'"
    using b_conc_exec_deterministic[OF 1(2) 1(5)] by auto
  have "t + 1 = maxtime \<or> t + 1 < maxtime"
    using `t < maxtime` by auto
  moreover
  { assume "t + 1 = maxtime "
    moreover hence "next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>"
      using `maxtime < next_time t \<tau>'` unfolding next_state2_def Let_def comp_def
      by (metis \<open>\<tau>2 = \<tau>'\<close> dom_eq_empty_conv next_time_at_least2 override_on_emptyset zero_fun_def zero_option_def)
    moreover have "\<tau>2(t + 1 := 0) = \<tau>'"
      using until_next_time_zero`maxtime < next_time t \<tau>'` `t + 1 = maxtime` unfolding `\<tau>2 = \<tau>'` 
      by fastforce 
    ultimately have ?case
      using 1(3) bau_suc by blast }
  moreover
  { assume "t + 1 < maxtime "  
    have nqu: "\<not> quiet (\<tau>2(t + 1 := 0)) (next_event2 (t + 1) \<tau>2 \<sigma>)"
      by (metis "1.prems"(4) \<open>\<tau>2 = \<tau>'\<close> \<open>t + 1 < maxtime\<close> fun_upd_idem_iff leD less_or_eq_imp_le
      less_trans next_time_at_least2 next_time_def quiet_def)
    have mt: " maxtime < next_time (t + 1) \<tau>2 "
      unfolding `\<tau>2 = \<tau>'` by (metis "1.prems"(4) \<open>t + 1 < maxtime\<close> next_time_def not_less_iff_gr_or_eq)
    hence "next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>"
      using `t + 1 < maxtime` unfolding next_state2_def Let_def 
      by (metis dom_eq_empty_conv dual_order.strict_trans next_time_at_least2 override_on_emptyset
      zero_fun_def zero_option_def)
    hence "next_event2 (t + 1) \<tau>2 \<sigma> = {}"
      by (simp add: next_event2_alt_def)
    hence "t + 1 , next_state2 (t + 1) \<tau>2 \<sigma> , next_event2 (t + 1) \<tau>2 \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>2(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>2"
      using b_conc_exec_empty_event 
      by (metis "1.prems"(4) \<open>\<tau>2 = \<tau>'\<close> \<open>t + 1 < maxtime\<close> dual_order.strict_trans fun_upd_idem_iff next_time_at_least2)
    then obtain \<theta>'' where "res = (maxtime, \<sigma>, \<theta>'', \<tau>')" and
      *: "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k)"
      using 1(4)[OF _ nqu `t + 1 < maxtime` mt `\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0`] 
      using \<open>\<tau>2 = \<tau>'\<close> \<open>next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>\<close> by metis
    have "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k)"
    proof (rule+)
      fix s k
      assume "k \<le> maxtime" consider "k \<le> t" | "k = t + 1" | "t + 1 < k" by linarith
      thus "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>'' s k "
      proof (cases)
        case 1
        then show ?thesis using * `t < maxtime` 
          by (smt \<open>k \<le> maxtime\<close> add_le_same_cancel1 comp_apply fun_upd_other leD
          less_numeral_extra(1) to_signal_equal_when_trans_equal_upto)
      next
        case 2
        then show ?thesis 
          using * `t < maxtime` `\<forall>n\<ge>t. \<theta> n = 0`
          by (smt add.commute add_diff_cancel_left' add_le_same_cancel1 discrete fun_upd_same hi
          not_le not_one_le_zero signal_of_less trans_some_signal_of)
      next
        case 3
        then show ?thesis 
          using * `t + 1 < maxtime` `k \<le> maxtime`            
          by (smt "1.hyps"(1) discrete fun_upd_apply hi nat_less_le signal_of_less_ind
          trans_some_signal_of)
      qed
    qed      
    hence ?case
      using \<open>res = (maxtime, \<sigma>, \<theta>'', \<tau>')\<close> by blast }
  ultimately show ?case by auto
next
  case (2 maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case by auto
qed

(* lemma b_simulate_fin_and_suc_semi_equivalent':
  assumes "maxtime, t ,\<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  assumes "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes "\<forall>n. t < n \<longrightarrow>  \<theta>1 n = 0" and "\<forall>n. t < n \<longrightarrow>  \<theta>2 n = 0"
  assumes "conc_stmt_wf cs" 
  assumes "\<forall>n. n < t \<longrightarrow>  \<tau> n = 0"
  shows   "get_state res1 = get_state res2 \<and> get_trans res1 = get_trans res2
          \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res1) s k = signal_of (def s) (get_beh res2) s k)"
  using assms
proof (induction arbitrary: \<theta>2 rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  show ?case  
    using 1(7-13) 1(1) 1(3-5) 
  proof (induction arbitrary: res \<theta> \<tau>' rule:b_simulate_fin_suc.induct)
    case (1 t maxtime \<sigma> \<gamma> \<theta>1 def cs \<tau> \<tau>2 res')
    have "\<tau>' = \<tau>2"
      using 1 b_conc_exec_deterministic_weaker by (metis (no_types, lifting))
    have "t < next_time t \<tau>'"
      using "1.prems"(4) "1.prems"(5) "1.prems"(6) "1.prems"(8) nonneg_delay_conc_next_time_strict by blast
    hence " \<forall>n\<le>t. \<tau>' n = 0"
      using  next_time_at_least2 order.strict_trans1 by blast
    hence big: "\<forall>n\<le>t + 1. (\<tau>2(t + 1 := 0)) n = 0"
      using `\<tau>' = \<tau>2` by auto
    have "t + 1 = maxtime \<or> t + 1 < maxtime"
      using "1.prems"(7) by linarith
    moreover
    { assume "t + 1 = maxtime"
      have "get_state res' = next_state2 (t + 1) \<tau>2 \<sigma>"
        apply (rule bau_suc[OF 1(3)]) using `t + 1 = maxtime` by auto
      also have "... = next_state2 (t + 1) \<tau>' \<sigma>"
        using `\<tau>' = \<tau>2` by auto
      finally have "get_state res' = next_state2 (t + 1) \<tau>' \<sigma>"
        by auto
      have "next_time t \<tau>' = maxtime" and "next_time t \<tau>' = t + 1"
        using `next_time t \<tau>' \<le> maxtime` `t < next_time t \<tau>'` `t + 1 = maxtime` by auto
      have "get_state res = next_state t \<tau>' \<sigma>"
        apply (rule bau[OF 1(14)]) using `next_time t \<tau>' = maxtime` by auto
      also have "... = next_state2 (t + 1) \<tau>' \<sigma>"
        unfolding next_state_def next_state2_def `next_time t \<tau>' = t + 1` by auto
      finally have conj1: "get_state res = get_state res'"
        using `get_state res' = next_state2 (t + 1) \<tau>' \<sigma>` by fastforce 
      have "get_trans res' = \<tau>2(t + 1 := 0)"
        apply (rule bau_suc[OF 1(3)]) using `t + 1 = maxtime` by auto
      also have "... = \<tau>'(next_time t \<tau>' := 0)"
        using `\<tau>' = \<tau>2` `next_time t \<tau>' = maxtime` `t + 1 = maxtime` by auto
      also have "... = get_trans res"
        apply (rule bau[OF 1(14)]) using `next_time t \<tau>' = maxtime` by auto
      finally have conj2: "get_state res = get_state res' \<and> get_trans res = get_trans res'"
        using conj1 by auto 
      have "get_beh res' = \<theta>1(t := Some \<circ> \<sigma>)"
        apply (rule bau_suc[OF 1(3)]) using `t + 1 = maxtime` by auto
      moreover have "get_beh res = \<theta>(t := Some o \<sigma>)"
        apply (rule bau[OF 1(14)]) using `next_time t \<tau>' = maxtime` `t < next_time t \<tau>'`
        unfolding add_to_beh_def sledgehammer
      moreover have "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k"
      proof (rule+)
        fix s k
        assume "k \<le> maxtime"
        hence "k \<le> t \<or> t < k"
          using `t < next_time t \<tau>'` by linarith
        moreover
        { assume "k \<le> t"
          hence "signal_of (def s) \<theta> s k = signal_of (def s) \<theta>1 s k"        
            using "1.prems"(1) by auto
          hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
            using `k \<le> t` apply (cases "k = t")
            by(metis fun_upd_same trans_some_signal_of) (smt fun_upd_apply leD nat_less_le o_apply order_refl to_signal_equal_when_trans_equal_upto) }
        moreover
        { assume " t < k"
          hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (\<theta>1 (t := Some o \<sigma>)) s k"
            using `\<forall>n\<ge>t. \<theta>1 n = 0` `\<forall>n\<ge>t. \<theta> n = 0` `t < k`
            by (smt dual_order.strict_implies_order fun_upd_apply neq_iff signal_of_less_ind trans_some_signal_of) }
        ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
          by auto
      qed 
      ultimately have "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res') s k = signal_of (def s) (get_beh res) s k"
        by auto
      hence ?case using conj2 by auto }
    moreover
    { assume "t + 1 < maxtime "
      have hist: "\<forall>s k. k \<le> t + 1 \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
      proof (rule+)
        fix s k
        assume "k \<le> t + 1" hence "k < t \<or> k = t \<or> k = t + 1" by auto
        moreover
        { assume "k < t"
          hence " signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta> s k"
            by (metis dual_order.refl fun_upd_other leD signal_of_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) \<theta>1 s k"
            using 1(5) `k < t` by auto
          also have "... = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k"
            using `k < t` by (metis dual_order.refl fun_upd_other leD
            signal_of_equal_when_trans_equal_upto) 
          finally have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
            by auto }
        moreover
        { assume "k = t"
          hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
            by (metis fun_upd_same trans_some_signal_of) }
        moreover
        { assume "k = t + 1"
          have " inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
          proof (rule inf_time_someI)
            show "t \<in> dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s)"
              by (simp add: domIff to_trans_raw_sig_def)
          next
            { fix j 
              assume "j \<in> dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s)" and "j > t"
              hence  "j \<in> dom (to_trans_raw_sig \<theta> s)"
                by (simp add: domIff to_trans_raw_sig_def)
              with 1(6) have "False"
                unfolding to_trans_raw_sig_def dom_def zero_fun_def zero_option_def  using \<open>t < j\<close> 
                by auto
              hence "j > k"
                by auto }
            thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
              using not_le by blast
          qed (auto simp add: `k = t + 1`)
          moreover have " inf_time (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
          proof (rule inf_time_someI)
            show "t \<in> dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s)"
              by (simp add: domIff to_trans_raw_sig_def)
          next
            { fix j 
              assume "j \<in> dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s)" and "j > t"
              hence  "j \<in> dom (to_trans_raw_sig \<theta>1 s)"
                by (simp add: domIff to_trans_raw_sig_def)
              with 1(7) have "False"
                unfolding to_trans_raw_sig_def dom_def zero_fun_def zero_option_def  using \<open>t < j\<close> 
                by auto
              hence "j > k"
                by auto }
            thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
              using not_le by blast
          qed (auto simp add: `k = t + 1`)
          ultimately have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
            unfolding to_signal_def comp_def to_trans_raw_sig_def by auto }
        ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k"
          by auto
      qed
      have "t + 1 < next_time t \<tau>' \<or> t + 1 = next_time t \<tau>'"
        using \<open>t < next_time t \<tau>'\<close> by linarith
      moreover
      { assume "t + 1 < next_time t \<tau>'"
        have "\<forall>n\<ge>t + 1. (\<theta>(t := Some o \<sigma>)) n = 0" and "\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0"
          by (simp add: "1.prems"(2-3))+
        note IH0 = 1(4)[OF hist this `nonneg_delay_conc cs` `conc_stmt_wf cs` `\<forall>n\<le>t + 1. (\<tau>2(t + 1 := 0)) n = 0` `t + 1 < maxtime`]
        have "next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>"
          using `\<tau>' = \<tau>2` `t + 1 < next_time t \<tau>'` 
          by (simp add: next_state2_def next_time_at_least2 zero_fun_def zero_option_def)
        have "next_event2 (t + 1) \<tau>2 \<sigma> = {}"
          using `\<tau>' = \<tau>2` `t + 1 < next_time t \<tau>'` 
          by (metis (full_types) \<open>next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>\<close> empty_Collect_eq next_event2_alt_def)
        hence "t + 1 , next_state2 (t + 1) \<tau>2 \<sigma> , next_event2 (t + 1) \<tau>2 \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>2(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>'"
          by (metis \<open>\<tau>' = \<tau>2\<close> \<open>t + 1 < next_time t \<tau>'\<close> b_conc_exec_empty_event fun_upd_idem next_time_at_least2)
        note IH1 = IH0[OF this]
        have "next_time (t + 1) \<tau>' \<le> maxtime"
          using `t + 1 < next_time t \<tau>'` `next_time t \<tau>' \<le> maxtime` 
          by (metis less_imp_neq next_time_def)
        note IH2 = IH1[OF this]
        have " next_time t \<tau>' = next_time (t + 1) \<tau>'"
          by (metis \<open>t + 1 < next_time t \<tau>'\<close> le_refl next_time_def not_le)
        moreover have "next_state (t + 1) \<tau>' (next_state2 (t + 1) \<tau>2 \<sigma>) = next_state t \<tau>' \<sigma>"
          using `next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>`  by (simp add: calculation next_state_def)
        moreover have "next_event (t + 1) \<tau>' (next_state2 (t + 1) \<tau>2 \<sigma>) = next_event t \<tau>' \<sigma>"
          using `next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>`  by (simp add: calculation(1) next_event_def)
        moreover have "add_to_beh (next_state2 (t + 1) \<tau>2 \<sigma>) (\<theta>(t := Some \<circ> \<sigma>)) (t + 1) (next_time (t + 1) \<tau>') = 
                        \<theta>(t := Some o \<sigma>, t + 1 := Some o \<sigma>)"
          by (metis \<open>next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>\<close> \<open>t + 1 < next_time t \<tau>'\<close> add_to_beh_def calculation(1))
        have imp: " \<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some o \<sigma>)) s k"
        proof (rule+)
          fix s k
          assume "k \<le> next_time t \<tau>'"
          hence "k \<le> t \<or> k = t + 1 \<or> t + 1 < k"
            using `t < next_time t \<tau>'` by linarith
          moreover
          { assume "k \<le> t"
            hence "signal_of (def s) \<theta> s k = signal_of (def s) \<theta> s k"        
              using 1(5) by blast
            hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some o \<sigma>)) s k"
              using `k \<le> t` apply (cases "k = t")
              by (smt add_le_same_cancel1 fun_upd_other leD less_numeral_extra(1) signal_of_equal_when_trans_equal_upto)+ }
          moreover
          { assume " k = t + 1"
            hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (\<theta> (t := Some o \<sigma>, t + 1 := Some o \<sigma>)) s k"
              using `\<forall>n\<ge>t. \<theta> n = 0`
              by (metis (no_types, hide_lams) \<open>\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0\<close>
              add_diff_cancel_left' diff_diff_cancel fun_upd_same le_add1 order_refl
              signal_of_less trans_some_signal_of) }
          moreover 
          { assume " t + 1 < k"
            have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (\<theta> (t := Some o \<sigma>, t + 1 := Some o \<sigma>)) s k"
            proof -
              have *: "inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
              proof (rule inf_time_someI)
                { fix j
                  assume "j \<in> dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s)" and "j > t"
                  hence "j \<in> dom (to_trans_raw_sig \<theta> s)"
                    unfolding to_trans_raw_sig_def fun_upd_def by auto
                  hence "False"
                    using `\<forall>n\<ge>t. \<theta> n = 0` `j > t` unfolding to_trans_raw_sig_def zero_fun_def zero_option_def dom_def 
                    by auto
                  hence "j > k"
                    by auto }
                thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
                  using leD le_less_linear by blast
                show "t \<le> k"
                  using `t + 1 < k`  by linarith
              qed (auto simp add: to_trans_raw_sig_def)
              have "inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x)))) s k = Some (t + 1)"
              proof (rule inf_time_someI)
                { fix j 
                  assume "j \<in> dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x))) s)" and "t + 1 < j"
                  hence  "j \<in> dom (to_trans_raw_sig \<theta> s)"
                    unfolding to_trans_raw_sig_def fun_upd_def dom_def by auto
                  hence "False"
                    using `\<forall>n\<ge>t. \<theta> n = 0` `t + 1 < j` unfolding to_trans_raw_sig_def dom_def zero_fun_def zero_option_def
                    by auto
                  hence "k < j"
                    by auto }
                thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t + 1"
                  using not_le by blast
                show "t + 1 \<le> k"
                  using `t + 1 < k` by auto
              qed (auto simp add: to_trans_raw_sig_def)
              hence "signal_of (def s) (\<theta> (t := Some o \<sigma>, t + 1 := Some o \<sigma>)) s k = \<sigma> s"
                unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
              also have "... = signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k"
                using * unfolding to_signal_def comp_def  to_trans_raw_sig_def by auto
              finally show ?thesis
                by auto
            qed }
          ultimately show "signal_of (def s) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k"
            by (metis `t < next_time t \<tau>'` add_to_beh_def)
        qed
        have imp2: "\<forall>n\<ge>next_time t \<tau>'. add_to_beh \<sigma> \<theta> t (next_time t \<tau>') n = 0"
          using `\<forall>n\<ge>t. \<theta> n = 0` 
          by (metis `t < next_time t \<tau>'` \<open>\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0\<close> \<open>t + 1 < next_time t \<tau>'\<close>
          add_to_beh_def less_le_trans nat_less_le)
        have imp3: "\<forall>n\<ge>next_time t \<tau>'. (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) n = 0"
          using `\<forall>n\<ge>t. \<theta> n = 0` \<open>t + 1 < next_time t \<tau>'\<close> by auto
        have imp4: "\<forall>n\<le>next_time t \<tau>'. (\<tau>'(next_time t \<tau>' := 0)) n = 0"
          by (simp add: le_less next_time_at_least2)
        obtain res3 where res3: "maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , \<theta>(t := Some o \<sigma>, t + 1 := Some o \<sigma>), def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> res3"
          using only_context_matters_b_simulate_fin_progress[OF 1(14) imp imp2 imp3 imp4] by blast
        have "get_state res3 = get_state res \<and> get_trans res3 = get_trans res
             \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res3) s k = signal_of (def s) (get_beh res) s k)"
          using b_simulate_fin_deterministic_weaker[OF 1(14) res3 imp imp2 imp3 imp4] by auto
        with IH2 res3 have ?case 
          by (metis \<open>add_to_beh (next_state2 (t + 1) \<tau>2 \<sigma>) (\<theta>(t := Some \<circ> \<sigma>)) (t + 1) (next_time (t
          + 1) \<tau>') = \<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)\<close> calculation(1) calculation(2)
          calculation(3)) }
      moreover
      { assume "t + 1 = next_time t \<tau>'"
        have "\<tau>2 = \<tau>'"
          using b_conc_exec_deterministic_weaker[OF 1(2) 1(12)] 1(5) by auto
        have star: " maxtime, t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta>(t := Some o \<sigma>), def \<turnstile> <cs , \<tau>'(t + 1 := 0)> \<leadsto> res"
          using 1(14) `t + 1 = next_time t \<tau>'` unfolding next_state2_def next_state_def Let_def next_event2_def next_event_def
          add_to_beh_def by presburger
        note IH = 1(4)[OF hist]
        have "\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0" and "\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0"
          using `\<forall>n\<ge>t. \<theta> n = 0` `\<forall>n\<ge>t. \<theta>1 n = 0` by auto
        have helper: "\<forall> s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some o \<sigma>, t + 1 := Some \<circ> next_state t \<tau>' \<sigma>)) s k = 
                                      signal_of (def s) (\<theta>1(t := Some o \<sigma>, t + 1 := Some \<circ> next_state t \<tau>' \<sigma>)) s k"
        proof (rule+)
          fix s k
          assume "k \<le> maxtime"
          hence "k \<le> t + 1 \<or> t + 1 < k"
            using `t < next_time t \<tau>'` by linarith
          moreover
          { assume "k \<le> t + 1"
            hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k"        
              using hist by auto
            hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k = 
                   signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k"
              using `k \<le> t + 1` apply (cases "k = t + 1")
              by(metis fun_upd_same trans_some_signal_of) (smt fun_upd_apply leD nat_less_le o_apply order_refl to_signal_equal_when_trans_equal_upto) }
          moreover
          { assume " t + 1 < k"
            hence "signal_of (def s) (\<theta>(t := Some o \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k = 
                   signal_of (def s) (\<theta>1 (t := Some o \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k"
              using `\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0` `\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0` `t + 1 < k`
              by (smt dual_order.strict_implies_order fun_upd_apply neq_iff signal_of_less_ind trans_some_signal_of) }
          ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k = 
                           signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>, t + 1 := Some o next_state t \<tau>' \<sigma>)) s k"
            by auto
        qed 
        note IH2 = IH[OF `\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0` `\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0` `nonneg_delay_conc cs` `conc_stmt_wf cs` big `t + 1 < maxtime`]
        consider (quiet) "quiet (\<tau>'(t + 1 := 0)) (next_event t \<tau>' \<sigma>)" | (nonquiet) "\<not> quiet (\<tau>'(t + 1 := 0)) (next_event t \<tau>' \<sigma>)"
          by auto
        hence ?case
        proof (cases)
          case quiet
          have *: "get_state res = next_state t \<tau>' \<sigma> \<and> get_trans res = 0 \<and> get_beh res = \<theta>(t := Some o \<sigma>, t + 1 := Some \<circ> next_state t \<tau>' \<sigma>)"
            using 1(14) case_quiesce[OF `t + 1 < maxtime` quiet] `t < next_time t \<tau>'` unfolding `t + 1 = next_time t \<tau>'` add_to_beh_def 
            by presburger
          have "next_event2 (t + 1) \<tau>2 \<sigma> = {} \<and> \<tau>2 (t + 1 := 0) = 0"
            using quiet unfolding next_event_def next_event2_def Let_def `t + 1 = next_time t \<tau>'` `\<tau>2 = \<tau>'` quiet_def comp_def 
            by presburger+
          with quiet_fast_forward[OF 1(3) _ `t + 1 < maxtime` `\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0`]
          show ?thesis
            using * 
            by (metis (mono_tags, lifting) helper \<open>\<tau>2 = \<tau>'\<close> \<open>t + 1 = next_time t \<tau>'\<close> comp_apply fst_conv
            next_state2_def next_state_def quiet_def snd_conv)
        next
          case nonquiet
          obtain \<tau>3 where tau3: "t + 1 , next_state2 (t + 1) \<tau>2 \<sigma> , next_event2 (t + 1) \<tau>2 \<sigma> , \<theta>1(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>2(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>3"
            using 1(3) bau_suc `t + 1 < maxtime` by blast
          have h1: "(next_event2 (t + 1) \<tau>' \<sigma>) = next_event t \<tau>' \<sigma>"
            using \<open>t + 1 = next_time t \<tau>'\<close> next_event2_def next_event_def by fastforce
          have "maxtime < next_time (t + 1) \<tau>3 \<or> maxtime \<ge> next_time (t + 1) \<tau>3"
            by auto
          moreover
          { assume "maxtime < next_time (t + 1) \<tau>3"
            moreover have "\<not> quiet (\<tau>2(t + 1 := 0)) (next_event2 (t + 1) \<tau>2 \<sigma>)"
              using nonquiet by (metis \<open>\<tau>' = \<tau>2\<close> \<open>t + 1 = next_time t \<tau>'\<close> next_event2_def next_event_def)
            ultimately have *: "get_state res' = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res' = \<tau>3
                            \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> next_state2 (t + 1) \<tau>2 \<sigma>)) s k = signal_of (def s) (get_beh res') s k)" 
              using not_quiet_fast_forward[OF 1(3) tau3 _ `t + 1 < maxtime`] \<open>\<forall>n\<ge>t + 1. (\<theta>1(t := Some \<circ> \<sigma>)) n = 0\<close> 
              by auto
            have h2 : "t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>'(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>3 "
              using only_context_matters_for_progress_conc_hist[OF tau3] hist  b_conc_exec_deterministic_weaker[OF tau3]
              unfolding `\<tau>2 = \<tau>'` by metis
            have h3: "next_state2 (t + 1) \<tau>' \<sigma> = next_state t \<tau>' \<sigma>"
              by (metis \<open>t + 1 = next_time t \<tau>'\<close> next_state2_def next_state_def)
            have "get_state res = next_state t \<tau>' \<sigma> \<and> get_trans res = \<tau>3 \<and> get_beh res = \<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> next_state2 (t + 1) \<tau>' \<sigma>)"
              apply (rule bau[OF star])
              using `t + 1 < maxtime` nonquiet h1 h2 `maxtime < next_time (t + 1) \<tau>3` h3 
              using b_conc_exec_deterministic not_le apply blast
              using b_conc_exec_deterministic h2 h3 apply fastforce
              using h1 nonquiet \<open>t + 1 < maxtime\<close> by auto
            moreover have "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res) s k = signal_of (def s) (get_beh res') s k)"
              using helper *
              using \<open>\<tau>' = \<tau>2\<close> calculation h3 by auto
            ultimately have ?thesis
              using \<open>\<tau>' = \<tau>2\<close> * h3 by metis }
          moreover
          { assume "maxtime \<ge> next_time (t + 1) \<tau>3"
            have tau3': "t + 1 , next_state2 (t + 1) \<tau>2 \<sigma> , next_event2 (t + 1) \<tau>2 \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>2(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>3"
              using tau3 only_context_matters_for_progress_conc_hist[OF tau3] hist  b_conc_exec_deterministic_weaker[OF tau3]
              by metis
            have "maxtime, next_time (t + 1)
            \<tau>3 , next_state (t + 1) \<tau>3
                  (next_state2 (t + 1) \<tau>2
                    \<sigma>) , next_event (t + 1) \<tau>3
                          (next_state2 (t + 1) \<tau>2 \<sigma>) , add_to_beh (next_state2 (t + 1) \<tau>2 \<sigma>) (\<theta>(t := Some \<circ> \<sigma>)) (t + 1) (next_time (t + 1) \<tau>3), def \<turnstile> <cs , \<tau>3
  (next_time (t + 1) \<tau>3 := 0)> \<leadsto> res"
              apply (rule bau[OF star])
              using star tau3' h1 `maxtime \<ge> next_time (t + 1) \<tau>3` `t + 1 < maxtime` nonquiet unfolding `\<tau>2 = \<tau>'` 
              using b_conc_exec_deterministic apply blast
              using \<open>\<tau>' = \<tau>2\<close> \<open>next_time (t + 1) \<tau>3 \<le> maxtime\<close> case_bau star tau3' apply blast
              using h1 nonquiet \<open>t + 1 < maxtime\<close> by auto        
            hence ?thesis
              using IH2[OF tau3' `maxtime \<ge> next_time (t + 1) \<tau>3`] by blast }
          ultimately show ?thesis by auto
        qed }
      ultimately have ?case by auto }
    ultimately show ?case by blast
  qed (auto) 
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta>1 def cs \<tau>')
  show ?case 
    using 2(5) 2(3-4) 2(6-8) `t < maxtime`
  proof (induction arbitrary: \<theta>1 rule:b_simulate_fin_suc.induct)
    case (1 t maxtime \<sigma> \<gamma> \<theta>2 def cs \<tau> \<tau>2 res)
    hence "\<tau>' = \<tau>2"
      by (metis b_conc_exec_deterministic_weaker) 
    have "t + 1 < next_time t \<tau>'"
      using 1 by auto
    hence "\<tau>' \<noteq> 0"
      unfolding next_time_def by auto
    hence "next_time t \<tau>' = next_time (t + 1) \<tau>'"
      unfolding next_time_def by auto
    hence "maxtime < next_time (t + 1) \<tau>'"
      using 1 by auto
    have "next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>"
      unfolding sym[OF `\<tau>' = \<tau>2`] using `t + 1 < next_time t \<tau>'`
      by (simp add: next_state2_def next_time_at_least2 zero_fun_def zero_option_def)
    have " next_event2 (t + 1) \<tau>2 \<sigma> = {}"
      unfolding sym[OF `\<tau>' = \<tau>2`] using `t + 1 < next_time t \<tau>'`
      by (simp add: next_event2_def next_time_at_least2 zero_fun_def zero_option_def)
    have "t + 1 = maxtime \<or> t + 1 < maxtime"
      using 1 by auto
    moreover
    { assume "t + 1 = maxtime "
      have helper: "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k)"
      proof (rule+)
        fix s k
        assume "k \<le> maxtime" hence "k < t \<or> k = t \<or> k = t + 1" using `t + 1 = maxtime` by auto
        moreover
        { assume " k < t"
          hence "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) \<theta>1 s k"
            by (metis dual_order.refl fun_upd_other min.absorb2 min.strict_order_iff signal_of_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) \<theta>2 s k"
            using 1(7) `k < t` by auto
          also have "... = signal_of (def s) (\<theta>2 (t:= Some o \<sigma>)) s k"
            by (smt \<open>k < t\<close> fun_upd_other neq_iff not_le signal_of_equal_when_trans_equal_upto)
          finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
            by auto }
        moreover
        { assume "k = t \<or> k = t + 1"
          hence "signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k = \<sigma> s"
          proof (cases "k = t")
            case True
            then show ?thesis  by (meson fun_upd_same trans_some_signal_of)
          next
            case False
            have "inf_time (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
            proof (rule inf_time_someI)
              { fix j
                assume "j\<in>dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s)"
                assume "j > t"
                hence  "j \<notin> dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s)"
                  using `\<forall>n\<ge>t. \<theta>1 n = 0`  by (simp add: domIff to_trans_raw_sig_def zero_fun_def zero_option_def)
                hence "j \<ge> k"
                  using \<open>j \<in> dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s)\<close> by blast }
              thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>1(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
                by (metis "1.prems"(4) domIff fun_upd_apply le_cases to_trans_raw_sig_def zero_fun_def zero_option_def)
              show "t \<le> k"
                using \<open>k = t \<or> k = t + 1\<close> le_add1 by blast
            qed (auto simp add: to_trans_raw_sig_def)
            then show ?thesis 
              unfolding to_signal_def comp_def by (auto simp add: to_trans_raw_sig_def)
          qed
          also have "... = signal_of (def s) (\<theta>2(t := Some o \<sigma>)) s k"
          proof (cases "k = t")
            case True
            then show ?thesis by (metis fun_upd_same trans_some_signal_of)
          next
            case False
            have "inf_time (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
            proof (rule inf_time_someI)
              { fix j
                assume "j\<in>dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x))) s)"
                assume "j > t"
                hence  "j \<notin> dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x))) s)"
                  using `\<forall>n\<ge>t. \<theta>2 n = 0`  by (simp add: domIff to_trans_raw_sig_def zero_fun_def zero_option_def)
                hence "j \<ge> k"
                  using \<open>j \<in> dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x))) s)\<close> by blast }
              thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
                by (metis "1.prems"(5) domIff fun_upd_apply le_cases to_trans_raw_sig_def zero_fun_def zero_option_def)
              show "t \<le> k"
                using \<open>k = t \<or> k = t + 1\<close> le_add1 by blast
            qed (auto simp add: to_trans_raw_sig_def)
            then show ?thesis 
              unfolding to_signal_def comp_def by (auto simp add: to_trans_raw_sig_def)
          qed
          finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
            by auto }
        ultimately show "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
          by auto
      qed
      have "get_state res = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res = \<tau>2(t + 1 := 0) \<and> get_beh res = \<theta>2(t := Some \<circ> \<sigma>)"
        apply (rule bau_suc[OF 1(3)])
        using `t + 1 = maxtime` by auto 
      hence "get_state res = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res = \<tau>' 
            \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        using \<open>\<tau>' = \<tau>2\<close> \<open>maxtime < next_time (t + 1) \<tau>'\<close> \<open>t + 1 = maxtime\<close> next_time_at_least2 helper by fastforce }
    moreover
    { assume "t + 1 < maxtime"
      have "t + 1 , next_state2 (t + 1) \<tau>2 \<sigma> , next_event2 (t + 1) \<tau>2 \<sigma> , \<theta>2(t := Some \<circ> \<sigma>), def  \<turnstile> <cs , \<tau>2(t + 1 := 0)> \<longrightarrow>\<^sub>c \<tau>'"
        apply (rule bau_suc[OF 1(3)]) using `t + 1 < maxtime`  
        by (metis \<open>\<tau>' = \<tau>2\<close> \<open>next_event2 (t + 1) \<tau>2 \<sigma> = {}\<close> \<open>t + 1 < next_time t \<tau>'\<close>
        b_conc_exec_empty_event fun_upd_idem next_time_at_least2)+
      with `maxtime < next_time (t + 1) \<tau>'` have *: "get_state res = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res = \<tau>' \<and> 
        (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> next_state2 (t + 1) \<tau>2 \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        using 1(4) 1(9) `t + 1 < maxtime` by fastforce 
      moreover have "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k"
      proof (rule+)
        fix s k
        assume "k \<le> maxtime" have "k < t \<or> k = t \<or> k = t + 1 \<or> t + 1 < k" by linarith
        moreover
        { assume "k < t"
          hence "signal_of (def s) (get_beh res) s k = signal_of (def s) (\<theta>2(t := Some o \<sigma>, t+1 := Some \<circ> next_state2 (t + 1) \<tau>2 \<sigma>)) s k"
            using * `k \<le> maxtime` by auto
          also have "... = signal_of (def s) \<theta>2 s k"
            by (smt \<open>k < t\<close> comp_def fun_upd_other le_add1 le_less_trans le_refl
            order.strict_iff_order to_signal_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) \<theta>1 s k"
            using "1.prems"(3) \<open>k < t\<close> by auto
          also have "... = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k" 
            by (metis \<open>k < t\<close> fun_upd_other leD order_refl signal_of_equal_when_trans_equal_upto)
          finally have " signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k"
            by auto }
        moreover
        { assume " k = t \<or> k = t + 1"
          hence "signal_of (def s) (get_beh res) s k = signal_of (def s) (\<theta>2(t := Some o \<sigma>, t+1 := Some \<circ> next_state2 (t + 1) \<tau>2 \<sigma>)) s k"
            using * `k \<le> maxtime` by auto
          also have "... = \<sigma> s"
            apply (cases " k = t")
            by (metis (mono_tags, lifting) \<open>k = t \<or> k = t + 1\<close> add_eq_self_zero fun_upd_other fun_upd_same trans_some_signal_of zero_neq_one)
               (metis \<open>k = t \<or> k = t + 1\<close> \<open>next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>\<close> fun_upd_same trans_some_signal_of)
          also have "... = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k"
            using 1(8)
            by (smt \<open>k = t \<or> k = t + 1\<close> add.commute add_diff_cancel_left' fun_upd_other fun_upd_same
                le_add1 signal_of_less trans_some_signal_of)
          finally have " signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k"
            by auto }
        moreover
        { assume " t + 1 < k"
          hence "signal_of (def s) (get_beh res) s k = signal_of (def s) (\<theta>2(t := Some o \<sigma>, t+1 := Some \<circ> next_state2 (t + 1) \<tau>2 \<sigma>)) s k"
            using * `k \<le> maxtime` by auto
          also have "... = signal_of (def s) (\<theta>2(t := Some o \<sigma>, t+1 := Some \<circ> \<sigma>)) s k"
            unfolding `next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>` by auto
          also have "... = \<sigma> s"
          proof -
            have " inf_time (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x)))) s k = Some (t + 1)"
            proof (rule inf_time_someI)
              { fix j 
                assume asm: "j\<in>dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x))) s)"
                assume "j > t + 1"
                hence  "j\<notin>dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x))) s)"
                  using `\<forall>n\<ge>t. \<theta>2 n = 0` unfolding to_trans_raw_sig_def fun_upd_def dom_def zero_fun_def zero_option_def 
                  by auto
                with asm have False by auto hence "j > k" by auto }
              thus "\<forall>j\<in>dom (to_trans_raw_sig (\<theta>2(t := \<lambda>x. Some (\<sigma> x), t + 1 := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t + 1"
                using not_le by blast
              show "t + 1 \<le> k"
                using `t + 1 < k` by auto
            qed (auto simp add: to_trans_raw_sig_def)
            thus ?thesis
              unfolding to_signal_def comp_def to_trans_raw_sig_def by auto
          qed
          also have "... = signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k"
            using `\<forall>n\<ge>t. \<theta>1 n = 0`
            by (smt \<open>t + 1 < k\<close> discrete fun_upd_other fun_upd_same neq_iff
            order.strict_implies_order signal_of_less_ind trans_some_signal_of)
          finally have " signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k"
            by auto }
        ultimately show "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k"
          by auto
      qed
      ultimately have "get_state res = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res = \<tau>' 
            \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        by auto }
    ultimately have "get_state res = next_state2 (t + 1) \<tau>2 \<sigma> \<and> get_trans res = \<tau>' \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
      using `\<tau>' = \<tau>2` by auto
    then show ?case 
      using \<open>next_state2 (t + 1) \<tau>2 \<sigma> = \<sigma>\<close> by (metis comp_apply fst_conv snd_conv)
  qed (auto)
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  show ?case 
    using 3(3-6) 3(1-2)
  proof (induction arbitrary: \<theta> rule: b_simulate_fin_suc.induct)
    case (1 t maxtime \<sigma> \<gamma> \<theta>' def cs \<tau> \<tau>' res)
    have "\<gamma> = {}" and "\<tau> = 0"
      using `quiet \<tau> \<gamma>` unfolding quiet_def by meson+
    have "\<tau>' = \<tau>"
      by (rule conc_cases_comb[OF 1(2)])
         (metis "1.hyps"(2) \<open>\<gamma> = {}\<close> b_conc_exec_deterministic b_conc_exec_empty_event)+
    hence "\<tau>'(t + 1 := 0) = \<tau>" and "\<tau>' = 0"
      using `\<tau> = 0` by (simp add: fun_upd_idem zero_fun_def)+
    moreover have "next_event2 (t + 1) \<tau>' \<sigma> = {}"
      using `\<tau>' = 0` unfolding next_event2_alt_def next_state2_def 
      by (simp add: zero_fun_def zero_option_def)
    ultimately have *: "quiet (\<tau>'(t + 1 := 0)) (next_event2 (t + 1) \<tau>' \<sigma>)"
      using `\<tau> = 0` unfolding quiet_def by auto
    have **: "\<forall>n\<ge>t + 1. (\<theta>'(t := Some \<circ> \<sigma>)) n = 0 "
      by (simp add: "1.prems"(3))
    have "next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>"
      by (simp add: \<open>\<tau>' = 0\<close> next_state2_def zero_fun_def zero_option_def)
    have ***: "(\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k)"
    proof (rule+)
      fix s k
      assume "k \<le> maxtime" hence "k < t \<or> k = t \<or> k = t + 1 \<or> t + 1 < k"  by linarith
      moreover
      { assume "k < t"
        hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = signal_of (def s) \<theta> s k"
          by (metis fun_upd_other leD le_refl signal_of_equal_when_trans_equal_upto)
        also have "... = signal_of (def s) \<theta>' s k"
          using 1(5) `k < t`  by auto
        also have "... = signal_of (def s) (\<theta>'(t := Some o \<sigma>)) s k"
          using `k < t` by (metis fun_upd_other leD le_refl signal_of_equal_when_trans_equal_upto)
        finally have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k"
          by auto }
      moreover
      { assume " k = t \<or> k = t + 1"
        hence "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = \<sigma> s"
        proof  (cases "k = t")
          case True
          then show ?thesis by (meson fun_upd_same trans_some_signal_of)
        next
          case False hence "k = t + 1" using `k = t \<or> k = t + 1` by auto
          have "inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
          proof (rule inf_time_someI)
            show " \<forall>j\<in>dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
              using `\<forall>n\<ge>t. \<theta> n = 0` by (metis domIff fun_upd_apply le_cases to_trans_raw_sig_def
              zero_fun_def zero_option_def)
            show "t \<le> k"
              by (simp add: \<open>k = t + 1\<close>)
          qed (auto simp add: to_trans_raw_sig_def)
          then show ?thesis 
            unfolding to_signal_def comp_def to_trans_raw_sig_def by auto 
        qed
        also have "... = signal_of (def s) (\<theta>'(t := Some o \<sigma>)) s k"  
        proof  (cases "k = t")
          case True
          then show ?thesis  by (metis fun_upd_same trans_some_signal_of)
        next
          case False hence "k = t + 1" using `k = t \<or> k = t + 1` by auto
          have "inf_time (to_trans_raw_sig (\<theta>'(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
          proof (rule inf_time_someI)
            show " \<forall>j\<in>dom (to_trans_raw_sig (\<theta>'(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
              using `\<forall>n\<ge>t. \<theta>' n = 0` by (metis domIff fun_upd_apply le_cases to_trans_raw_sig_def
              zero_fun_def zero_option_def)
            show "t \<le> k"
              by (simp add: \<open>k = t + 1\<close>)
          qed (auto simp add: to_trans_raw_sig_def)
          then show ?thesis 
            unfolding to_signal_def comp_def to_trans_raw_sig_def by auto 
        qed
        finally have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k"
          by auto }
      moreover
      { assume "t + 1 < k"
        have "inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
        proof (rule inf_time_someI)
          show " \<forall>j\<in>dom (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
            using `\<forall>n\<ge>t. \<theta> n = 0` 
            by (metis domIff fun_upd_apply le_cases to_trans_raw_sig_def zero_fun_def zero_option_def)
          show "t \<le> k"
            using \<open>t + 1 < k\<close> by linarith
        qed (auto simp add: to_trans_raw_sig_def)
        have "inf_time (to_trans_raw_sig (\<theta>'(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t"
        proof (rule inf_time_someI)
          show " \<forall>j\<in>dom (to_trans_raw_sig (\<theta>'(t := \<lambda>x. Some (\<sigma> x))) s). j \<le> k \<longrightarrow> j \<le> t"
            using `\<forall>n\<ge>t. \<theta>' n = 0` 
            by (metis domIff fun_upd_apply le_cases to_trans_raw_sig_def zero_fun_def zero_option_def)
          show "t \<le> k"
            using \<open>t + 1 < k\<close> by linarith
        qed (auto simp add: to_trans_raw_sig_def)
        have "signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k = \<sigma> s"
          unfolding to_signal_def comp_def 
          by (metis \<open>inf_time (to_trans_raw_sig (\<theta>(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t\<close> fun_upd_same
          option.sel option.simps(5) to_trans_raw_sig_def)
        also have "... = signal_of (def s) (\<theta>'(t := Some o \<sigma>)) s k"
          unfolding to_signal_def comp_def 
          by (metis \<open>inf_time (to_trans_raw_sig (\<theta>'(t := \<lambda>x. Some (\<sigma> x)))) s k = Some t\<close>
          fun_upd_same option.sel option.simps(5) to_trans_raw_sig_def)
        finally have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k"
          by auto }
      ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k"
        by auto
    qed
    have "t + 1 < maxtime \<or> t + 1 = maxtime"
      using 1 by auto
    moreover
    { assume "t + 1 = maxtime"
      have "get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> 
            (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        apply (rule bau_suc[OF 1(3)])
        using `t + 1 = maxtime` `\<tau>'(t + 1 := 0) = \<tau>` `\<tau>' = 0` `\<tau>' = \<tau>` by auto 
      hence "get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> 
            (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        using *** by auto }
    moreover
    { assume "t + 1 < maxtime"
      hence "get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> 
            (\<forall>s k. k \<le> maxtime \<longrightarrow>
             signal_of (def s) (\<theta>'(t := Some o \<sigma>, t + 1 := Some \<circ> next_state2 (t + 1) \<tau>' \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
        using * 1(4)[OF _ ** **] by fastforce
      moreover have "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>'(t := Some o \<sigma>, t + 1 := Some \<circ> next_state2 (t + 1) \<tau>' \<sigma>)) s k = 
                                           signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k"
        unfolding `next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>`
      proof (rule+)
        fix s k
        assume "k \<le> maxtime" hence "k < t + 1 \<or> t + 1 \<le> k" by auto
        moreover
        { assume "k < t + 1"
          hence " signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = 
                  signal_of (def s) (\<theta>'(t := Some o \<sigma>)) s k"
            by (smt fun_upd_other le_neq_implies_less le_refl order.asym signal_of_equal_when_trans_equal_upto)
          also have "... = signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k"
            using *** `k \<le> maxtime` by auto
          finally have "signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k"
            by auto }
        moreover
        { assume "t + 1 \<le> k"
          hence " signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = \<sigma> s"
            using `\<forall>n\<ge>t. \<theta>' n = 0` 
            by (smt "**" fun_upd_other fun_upd_same less_imp_le_nat nat_neq_iff signal_of_less_ind trans_some_signal_of)
          also have "... = signal_of (def s) (\<theta>(t := Some o \<sigma>)) s k"
            using `t + 1 \<le> k` `\<forall>n\<ge>t. \<theta> n = 0` 
            by (smt add_leD1 dual_order.strict_iff_order fun_upd_other fun_upd_same signal_of_less_ind trans_some_signal_of)
          finally have "signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k"
            by auto }
        ultimately show "signal_of (def s) (\<theta>'(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k"
          by auto
      qed
      ultimately have "get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> 
            (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
         by auto }
    ultimately have "get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)"
      by auto
    then show ?case 
      unfolding next_state2_def `\<tau>' = 0` Let_def 
      by (metis (mono_tags, hide_lams) \<open>next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>\<close> \<open>t + 1 < maxtime \<Longrightarrow> get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)\<close> \<open>t + 1 < maxtime \<or> t + 1 = maxtime\<close> \<open>t + 1 = maxtime \<Longrightarrow> get_state res = next_state2 (t + 1) \<tau>' \<sigma> \<and> get_trans res = 0 \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (get_beh res) s k)\<close> comp_eq_dest_lhs fst_conv snd_conv)
  qed (auto)
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    by (metis (no_types, lifting) bau_suc comp_def fstI nat_less_le sndI)
qed *)

(* lemma b_simulate_fin_and_suc_semi_equivalent:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  assumes "\<forall>n. t \<le> n \<longrightarrow>  \<theta> n = 0"
  assumes "nonneg_delay_conc cs"
  assumes "conc_stmt_wf cs" 
  assumes "\<forall>n. n \<le> t \<longrightarrow>  \<tau> n = 0"
  shows   "get_state res1 = get_state res2" and "get_trans res1 = get_trans res2"
      and "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res1) s k = signal_of (def s) (get_beh res2) s k"
  using b_simulate_fin_and_suc_semi_equivalent'[OF assms(1-2) _ assms(3) assms(3-6)]
  by auto

lemma b_simulate_fin_and_suc_semi_equivalent2: 
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  assumes "context_invariant t \<sigma> \<gamma> \<theta> def \<tau>"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  shows   "get_state res1 = get_state res2" and "get_trans res1 = get_trans res2"
      and "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res1) s k = signal_of (def s) (get_beh res2) s k"
proof -
  have *: "\<forall>n. t \<le> n \<longrightarrow> \<theta> n = 0" and **: "\<forall>n. n \<le> t \<longrightarrow> \<tau> n = 0"
    using assms(3) unfolding context_invariant_def by auto
  show "get_state res1 = get_state res2" and "get_trans res1 = get_trans res2" and "\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh res1) s k = signal_of (def s) (get_beh res2) s k"
    using b_simulate_fin_and_suc_semi_equivalent[OF assms(1-2) * assms(4-5) **]
    by auto
qed *)

lemma quiet_progress:
  assumes "quiet \<tau> \<gamma>" and "t < maxtime"
  shows   "\<exists>res. maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res"
  using assms
proof (induction "maxtime - t" arbitrary: maxtime t \<theta>)
  case 0 hence "maxtime = t" by auto 
  then show ?case 
    using "0.prems"(2)  by auto
next
  case (Suc x) hence "x = maxtime - (t + 1)"  by linarith
  hence IH: "t + 1 < maxtime \<Longrightarrow> \<exists>res. maxtime, t + 1, \<sigma> , \<gamma> , \<theta>(t := Some o \<sigma>), def \<turnstile> <cs , \<tau>> \<leadsto>s res"
    using Suc by auto
  have ex: "t  , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>"
    using `quiet \<tau> \<gamma>` b_conc_exec_empty_event unfolding quiet_def by metis
  moreover have lib0: "next_state2 (t + 1) \<tau> \<sigma> = \<sigma>"
    using `quiet \<tau> \<gamma>` unfolding quiet_def 
    by (metis dom_eq_empty_conv next_state2_def override_on_emptyset zero_fun_def zero_option_def)
  moreover have lib1: "next_event2 (t + 1) \<tau> \<sigma> = {}"
    unfolding next_event2_alt_def using calculation by auto
  moreover have lib2: "\<tau>(t + 1 := 0) = \<tau>" and lib3: "\<gamma> = {}"
    using `quiet \<tau> \<gamma>` unfolding quiet_def by (metis fun_upd_triv zero_fun_def)+
  note lib = lib0 lib1 lib2 lib3
  have "t + 1 < maxtime \<or> t + 1 = maxtime"
    using `t < maxtime` by auto
  moreover
  { assume "t + 1 < maxtime"
    then obtain res where "maxtime, t+1, \<sigma>, \<gamma>, \<theta>(t:=Some o \<sigma>), def \<turnstile> <cs, \<tau>> \<leadsto>s res"
      using IH by blast
    hence ?case
      apply (intro exI[where x="res"])
      apply (rule b_simulate_fin_suc.intros)
      using `t < maxtime` ex lib by auto }
  moreover
  { assume "t + 1 = maxtime "
    have ?case
      apply (intro exI[where x="(maxtime, \<sigma>, \<theta>(t := Some o \<sigma>), \<tau>)"])
      apply (rule b_simulate_fin_suc.intros(1)[OF `t < maxtime` ex])
      unfolding `t + 1 = maxtime` 
      using \<open>t + 1 = maxtime\<close> b_simulate_fin_suc.intros(2) lib0 lib2 by force }
  ultimately show ?case by auto
qed

lemma only_context_matters_for_simulate_fin_suc_progress:
  assumes   "maxtime, t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<leadsto>s res1"
  assumes   "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes   "\<forall>n\<ge>t. \<theta>1 n = 0" and "\<forall>n\<ge>t. \<theta>2 n = 0"
  shows     "\<exists>res2. maxtime, t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  using assms
proof (induction "maxtime - t" arbitrary: maxtime t \<sigma> \<gamma> \<theta>1 \<tau> \<theta>2)
  case 0
  then show ?case 
    by (metis b_simulate_fin_suc.intros(2) bau_suc zero_less_diff zero_order(3))
next
  case (Suc x)
  hence "t < maxtime" and "x = maxtime - (t + 1)" by linarith+
  then obtain \<tau>' where ex: "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and 
      "maxtime, 
          t + 1, 
            next_state2 (t + 1) \<tau>' \<sigma>, 
              next_event2 (t + 1) \<tau>' \<sigma>, 
                \<theta>1(t := Some o \<sigma>), 
                  def \<turnstile> <cs, \<tau>'(t + 1 := 0)> \<leadsto>s res1"
    using Suc(3) bau_suc by (metis b_simulate_fin_suc.simps nat_neq_iff)
  have ex2: "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
    using only_context_matters_for_progress_conc_hist[OF ex Suc(4)] 
          b_conc_exec_deterministic_weaker[OF ex _ Suc(4)] by blast
  have " \<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (\<theta>1(t:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>2(t:=Some o \<sigma>)) s k"
  proof (rule+)
    fix s k
    assume "k \<le> maxtime"
    have "k < t \<or> t \<le> k" by auto
    moreover
    { assume "k < t"
      hence "signal_of (def s) (\<theta>1(t:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>1) s k"
        by (metis dual_order.refl fun_upd_other leD signal_of_equal_when_trans_equal_upto)
      also have "... = signal_of (def s) \<theta>2 s k"
        using Suc.prems(2) \<open>k < t\<close> by auto
      also have "... = signal_of (def s) (\<theta>2(t:=Some o \<sigma>)) s k"
        using `k < t`
        by (metis dual_order.refl fun_upd_other leD signal_of_equal_when_trans_equal_upto) 
      finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
        by auto }
    moreover
    { assume " t \<le> k"
      hence "signal_of (def s) (\<theta>1(t:=Some o \<sigma>)) s k = \<sigma> s"
        using `\<forall>n\<ge>t. \<theta>1 n = 0` 
        by (smt dual_order.strict_implies_order fun_upd_other fun_upd_same neq_iff signal_of_less_ind trans_some_signal_of)
      also have "... = signal_of (def s) (\<theta>2(t:= Some o \<sigma>)) s k"
        using `\<forall>n\<ge>t. \<theta>2 n = 0` 
        by (smt \<open>t \<le> k\<close> fun_upd_other fun_upd_same less_imp_le_nat neq_iff signal_of_less_ind trans_some_signal_of)
      finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
        by auto }
    ultimately show "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
      by auto
  qed
  hence hist_same: "\<forall>s k. k \<le> t + 1 \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t:=Some o \<sigma>)) s k"
    using `t < maxtime`  by auto
  obtain res2 where res2: "maxtime, t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta>2(t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>'(t + 1 := 0)> \<leadsto>s res2"
    using Suc(1)[OF `x = maxtime - (t + 1)` \<open>maxtime, t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta>1 (t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>' (t + 1 := 0)> \<leadsto>s res1\<close>
                    hist_same] `\<forall>n\<ge>t. \<theta>1 n = 0` `\<forall>n\<ge>t. \<theta>2 n = 0` by auto
  then show ?case 
    apply(intro exI[where x="res2"])
    apply(rule b_simulate_fin_suc.intros(1)[OF `t < maxtime` ex2]) 
    by auto
qed

(* lemma only_context_matters_for_simulate_fin_suc_progress2:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "\<forall>n\<le>t. \<tau> n = 0"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "\<forall>n\<ge>t. \<theta> n = 0"
  shows   "\<exists>res2. maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  using assms
proof (induction rule: b_simulate_fin.inducts)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' res)
  have "\<forall>n\<le>next_time t \<tau>'. (\<tau>'(next_time t \<tau>' := 0)) n = 0"
    by (simp add: le_less next_time_at_least2)
  hence *: "\<exists>a. maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , add_to_beh \<sigma> \<theta> t (next_time t \<tau>'), def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto>s a"
    using 1(6) "1.prems"(2) "1.prems"(3-4) 
    by (metis (no_types, hide_lams) "1.hyps"(3) "1.prems"(1) add_to_beh_def
    dual_order.order_iff_strict fun_upd_apply less_irrefl_nat less_le_trans
    nonneg_delay_conc_next_time_strict)
  show ?case 
    using 1(1) 1(3-4) 1(7-9) * 1(10)
  proof (induction "maxtime - t" arbitrary: maxtime t \<gamma> \<tau> \<tau>' \<theta>)
    case (Suc x)  hence "x = maxtime - (t + 1)" by linarith
    have "t < next_time t \<tau>'"
      apply (rule nonneg_delay_conc_next_time_strict[OF _ Suc(4) Suc(7-8)])
      using Suc.prems(4) by blast
    have "t + 1 < next_time t \<tau>' \<or> t + 1 = next_time t \<tau>'"
      using `t < next_time t \<tau>'` by auto
    moreover
    { assume "t + 1 < next_time t \<tau>'"
      have ex: "t + 1 , \<sigma> , {} , \<theta>(t := Some o \<sigma>), def  \<turnstile> <cs , \<tau>'(t+1:=0)> \<longrightarrow>\<^sub>c \<tau>'(t+1:=0)"
        using b_conc_exec_empty_event by auto
      have h1: "next_time (t + 1) (\<tau>'(t + 1 := 0)) = next_time t \<tau>'"
        by (metis \<open>t + 1 < next_time t \<tau>'\<close> fun_upd_idem_iff nat_neq_iff next_time_at_least2 next_time_def)
      have h2: "next_state (t + 1) (\<tau>'(t + 1 := 0)) \<sigma> = next_state t \<tau>' \<sigma>"
        by (metis \<open>t + 1 < next_time t \<tau>'\<close> fun_upd_apply h1 nat_neq_iff next_state_def)
      have h3: "next_event (t + 1) (\<tau>'(t + 1 := 0)) \<sigma> = next_event t \<tau>' \<sigma>"
        by (metis (mono_tags, lifting) Collect_cong \<open>t + 1 < next_time t \<tau>'\<close> fun_upd_idem h1
        next_event_def next_time_at_least2)
      have "\<forall>n\<le>t + 1. (\<tau>'(t + 1 := 0)) n = 0"
        using \<open>t + 1 < next_time t \<tau>'\<close> le_less_trans next_time_at_least2 by fastforce
      have hist: "\<forall>s k. k\<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k =
                                              signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k"
      proof (rule+)
        fix s k
        assume "k \<le> next_time t \<tau>'"
        hence "k < t + 1 \<or> t + 1 \<le> k"
          using `t < next_time t \<tau>'` by linarith
        moreover
        { assume "k < t + 1"
          hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k =
                                              signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k"
            by (smt fun_upd_other leD min.strict_order_iff not_le_imp_less o_def to_signal_equal_when_trans_equal_upto) }
        moreover
        { assume "t + 1 \<le> k"
          hence "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = \<sigma> s"
            using `\<forall>n\<ge>t. \<theta> n = 0` 
            by (smt add_leD1 add_le_same_cancel1 fun_upd_other fun_upd_same less_imp_le_nat
            nat_neq_iff not_one_le_zero signal_of_less_ind trans_some_signal_of)
          also have "... = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            using `\<forall>n\<ge>t. \<theta> n = 0`  
            by (smt \<open>t + 1 \<le> k\<close> add_leE fun_upd_apply less_imp_le_nat less_irrefl_nat signal_of_less_ind trans_some_signal_of)
          finally have "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k =
                                              signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k"
            by auto }
        ultimately show "signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>)) s k =
                                              signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k"
          by auto
      qed
      have h4: " \<forall>n\<ge>next_time t \<tau>'. (\<theta>(t := Some \<circ> \<sigma>)) n = 0"
        using `\<forall>n\<ge>t. \<theta> n = 0`  using \<open>t < next_time t \<tau>'\<close> by auto
      have h5: "\<forall>n\<ge>next_time t \<tau>'. (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) n = 0"
        using `\<forall>n\<ge>t. \<theta> n = 0` `t + 1 < next_time t \<tau>'` by auto
      have h6: "\<tau>'(t + 1 := 0, next_time t \<tau>' := 0) = \<tau>'(next_time t \<tau>' := 0)"
        using \<open>t + 1 < next_time t \<tau>'\<close> next_time_at_least2 by fastforce
      obtain res where
        res: "b_simulate_fin_suc maxtime (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (\<theta>(t:=Some o \<sigma>)) def cs (\<tau>'(next_time t \<tau>' := 0)) res"
        using Suc `t < next_time t \<tau>'` unfolding add_to_beh_def by auto
      obtain res2 where res2: "b_simulate_fin_suc maxtime (next_time (t + 1) (\<tau>'(t + 1 := 0))) (next_state (t + 1) (\<tau>'(t + 1 := 0)) \<sigma>) (next_event (t + 1) (\<tau>'(t + 1 := 0)) \<sigma>)
         (add_to_beh \<sigma> (\<theta>(t := Some \<circ> \<sigma>)) (t + 1) (next_time (t + 1) (\<tau>'(t + 1 := 0)))) def cs (\<tau>'(t + 1 := 0, next_time (t + 1) (\<tau>'(t + 1 := 0)) := 0)) res2"
        using `t + 1 < next_time t \<tau>'` unfolding h1 h2 h3 h6 add_to_beh_def
        using only_context_matters_for_simulate_fin_suc_progress[OF res hist h4 h5] by presburger
      then obtain res3 where 
        "b_simulate_fin_suc maxtime (t + 1) \<sigma> {} (\<theta>(t := Some \<circ> \<sigma>)) def cs (\<tau>'(t + 1 := 0)) res3"
        using Suc(1)[OF `x = maxtime - (t + 1)` _ ex _ _ `nonneg_delay_conc cs` `conc_stmt_wf cs`]
        Suc.prems(3) \<open>t + 1 < next_time t \<tau>'\<close> res2 
        sledgehammer (add: Suc.prems(8) \<open>\<forall>n\<le>t + 1. (\<tau>'(t + 1 := 0)) n = 0\<close> add_diff_cancel_left' add_leD1
        diff_is_0_eq' fun_upd_apply h1 less_le_trans zero_neq_one)
        by (smt Suc.prems(8) \<open>\<forall>n\<le>t + 1. (\<tau>'(t + 1 := 0)) n = 0\<close> add_leD1 add_le_same_cancel1 fun_upd_apply h1 less_imp_le_nat less_le_trans not_one_le_zero)
      hence ?case
        apply (intro exI[where x="res3"])
        apply (rule b_simulate_fin_suc.intros(1)[OF `t \<le> maxtime` Suc(4)])
        by (metis (mono_tags) \<open>t + 1 < next_time t \<tau>'\<close> dom_eq_empty_conv empty_Collect_eq
        less_add_one next_event2_alt_def next_state2_def override_on_emptyset until_next_time_zero
        zero_fun_def zero_option_def) }
    moreover
    { assume "t + 1 = next_time t \<tau>'"
      hence ?case
        using Suc
      proof -
        have "\<forall>f fa n. next_event2 (next_time n fa) fa f = (next_event n fa f::'a set)"
          by (simp add: next_event2_def next_event_def)
        then show ?thesis
          by (metis (no_types) Suc_eq_plus1 \<open>Ex (b_simulate_fin_suc maxtime (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) def cs (\<tau>'(next_time t \<tau>' := 0)))\<close> \<open>t + 1 = next_time t \<tau>'\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> add_to_beh_def b_simulate_fin_suc.intros(1) lessI local.Suc(3) next_state2_def next_state_def)
      qed }
    ultimately show ?case
      by auto
  qed auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  show ?case 
    using 2(1) 2(3-4)
  proof (induction "maxtime - t" arbitrary: maxtime t \<gamma> \<tau> \<tau>' \<theta>)
    case (Suc x) hence "x = maxtime - (t + 1)" by linarith
    have ex: "t + 1 , \<sigma> , {} , \<theta>(t := Some o \<sigma>), def  \<turnstile> <cs , \<tau>'(t+1:=0)> \<longrightarrow>\<^sub>c \<tau>'(t+1:=0)"
      using b_conc_exec_empty_event by auto
    have "next_time (t + 1) (\<tau>'(t + 1 := 0)) = next_time t \<tau>'"
      by (metis (no_types, lifting) One_nat_def Suc.prems(1) Suc.prems(3) add.right_neutral add_Suc_right fun_upd_idem_iff less_trans_Suc next_time_at_least2 next_time_def not_less_eq)
    hence "maxtime < next_time (t + 1) (\<tau>'(t + 1 := 0))"
      by (simp add: Suc.prems(3))
    hence IH: "t + 1 < maxtime \<Longrightarrow> Ex (b_simulate_fin_suc maxtime (t + 1) \<sigma> {} (\<theta>(t := Some \<circ> \<sigma>)) def cs (\<tau>'(t + 1 := 0)))"
      using Suc(1)[OF `x = maxtime - (t + 1)` _ ex] by auto
    have "t + 1 < next_time t \<tau>'"
      using Suc.prems(1) Suc.prems(3) by linarith
    hence h1: " next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>" and h2: "next_event2 (t + 1) \<tau>' \<sigma> = {}"
      unfolding next_state2_def Let_def next_event2_alt_def
      by (simp add: next_time_at_least2 zero_fun_def zero_option_def)+
    have "t + 1 < maxtime \<or> t + 1 = maxtime"
      using Suc.prems(1) by linarith
    moreover
    { assume "t + 1 < maxtime"
      then obtain res where "maxtime, t + 1, \<sigma>, {}, (\<theta>(t:=Some o \<sigma>)), def \<turnstile> <cs, \<tau>'(t + 1 := 0)> \<leadsto>s res"  
        using IH by auto
      with Suc(4) have ?case
        using `t < maxtime` 
        apply (intro exI[where x="res"])
        apply (rule b_simulate_fin_suc.intros(1)[OF `t < maxtime` Suc(4)])
        unfolding h1 h2 by auto }
    moreover
    { assume " t + 1 = maxtime"
      then obtain res where "maxtime, t + 1, \<sigma>, {}, (\<theta>(t:=Some o \<sigma>)), def \<turnstile> <cs, \<tau>'(t + 1 := 0)> \<leadsto>s res"  
        using b_simulate_fin_suc.intros(2) by blast
      with Suc(4) have ?case
        using `t < maxtime` 
        apply (intro exI[where x="res"])
        apply (rule b_simulate_fin_suc.intros(1)[OF `t < maxtime` Suc(4)])
        unfolding h1 h2 by auto }
    ultimately show ?case
      by auto
  qed auto
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> def cs)
  then show ?case 
    using quiet_progress by auto
next
  case (4 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    using b_simulate_fin_suc.intros(2) by blast
qed *)

(* lemma b_sim_fin_suc_progress_for_b_sim_fin:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto>s res1"
  assumes "\<forall>n\<le>t. \<tau> n = 0"
  assumes "nonneg_delay_conc cs" and "conc_stmt_wf cs"
  assumes "\<forall>n\<ge>t. \<theta> n = 0"
  shows   "\<exists>res2. maxtime, t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<leadsto> res2"
  using assms
proof (induction rule: b_simulate_fin_suc.inducts)
  case (1 t maxtime \<sigma> \<gamma> \<theta> def cs \<tau> \<tau>' res)
  hence "\<forall>n\<le>t. \<tau>' n = 0"
    by (meson b_conc_exec_preserve_trans_removal_nonstrict)
  hence "\<forall>n\<le>t + 1. (\<tau>'(t + 1 := 0)) n = 0" by auto
  note IH = 1(4)[OF this `nonneg_delay_conc cs` `conc_stmt_wf cs`]
  have "\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0"
    using 1(8)  by auto
  note IH2 = IH[OF this]
  then obtain a where a: "maxtime, t + 1 , next_state2 (t + 1) \<tau>' \<sigma> , next_event2 (t + 1) \<tau>' \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>'(t + 1 := 0)> \<leadsto> a"
    by blast
  have "(\<not> quiet \<tau> \<gamma> \<and> next_time t \<tau>' \<le> maxtime) \<or> \<not> (\<not> quiet \<tau> \<gamma> \<and> next_time t \<tau>' \<le> maxtime)" (is "?case1 \<or> ?case2")
    by auto
  moreover
  { assume "?case2"
    hence ?case
      using 1(2)  by (meson "1.hyps"(1) b_simulate_fin.intros(2) b_simulate_fin.intros(3) not_le) }
  moreover
  { assume "?case1"
    have "t + 1 \<le> next_time t \<tau>'"
      by (metis "1.hyps"(2) "1.prems"(1) "1.prems"(2) "1.prems"(3) discrete nonneg_delay_conc_next_time_strict)
    then consider (match) "t + 1 = next_time t \<tau>'" | (not_match) "t + 1 < next_time t \<tau>'"
      by linarith
    hence ?case
    proof (cases)
      case match
      hence ns: "next_state2 (t + 1) \<tau>' \<sigma> = next_state t \<tau>' \<sigma>"
        by (simp add: next_state2_def next_state_def)
      have ne: "next_event2 (t + 1) \<tau>' \<sigma> = next_event t \<tau>' \<sigma>"
        using match next_event2_def next_event_def by fastforce
      have addtb: "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>(t := Some o \<sigma>)"
        unfolding add_to_beh_def  using \<open>t + 1 \<le> next_time t \<tau>'\<close> by auto
      have "maxtime, next_time t \<tau>', next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>,  add_to_beh \<sigma> \<theta> t (next_time t \<tau>'), def \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> a"
        using a match unfolding ns ne addtb   by simp
      then show ?thesis  
        using `?case1` 1(2)  using "1.hyps"(1) b_simulate_fin.intros(1) by blast
    next
      case not_match
      hence "next_event2 (t + 1) \<tau>' \<sigma> = {}"
        by (simp add: next_event2_def next_time_at_least2 zero_fun_def zero_option_def)
      moreover have "next_state2 (t + 1) \<tau>' \<sigma> = \<sigma>"
        using not_match
        by (simp add: next_state2_def next_time_at_least2 zero_fun_def zero_option_def)
      moreover have "\<tau>'(t+1:= 0) = \<tau>'"
        using not_match next_time_at_least2 by fastforce
      ultimately have *: "maxtime, t + 1 , \<sigma> , {}, \<theta>(t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>'> \<leadsto> a"
        using a by auto
      have "t + 1, \<sigma>, {}, \<theta>(t:=Some o \<sigma>), def \<turnstile> <cs, \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
        using b_conc_exec_empty_event by auto
      hence "maxtime, next_time (t + 1) \<tau>', next_state (t + 1) \<tau>' \<sigma>, next_event (t+1) \<tau>' \<sigma>,  add_to_beh \<sigma> (\<theta>(t:=Some o \<sigma>)) (t+1) (next_time t \<tau>'), def \<turnstile> <cs, \<tau>'(next_time (t+1) \<tau>' := 0)> \<leadsto> a"
        using * 
        by (smt \<open>\<not> quiet \<tau> \<gamma> \<and> next_time t \<tau>' \<le> maxtime\<close> case_bau less_irrefl_nat less_le_trans next_time_def not_match quiet_def)
      moreover have "next_state (t + 1) \<tau>' \<sigma> = next_state t \<tau>' \<sigma>"
        by (metis less_not_refl2 next_state_def next_time_def not_match)
      moreover have "next_time (t + 1) \<tau>' = next_time t \<tau>'"
        using not_match  by (metis less_irrefl_nat next_time_def)
      moreover have "next_event (t + 1) \<tau>' \<sigma> = next_event t \<tau>' \<sigma>"
        using not_match  by (metis (full_types) calculation(3) next_event_def)
      moreover have "add_to_beh \<sigma> (\<theta>(t:=Some o \<sigma>)) (t + 1) (next_time t \<tau>') = \<theta>(t := Some o \<sigma>, t+1 := Some o \<sigma>)"
        unfolding add_to_beh_def using not_match by auto
      ultimately have **: "maxtime, next_time t \<tau>', next_state t \<tau>' \<sigma>, next_event t \<tau>' \<sigma>,  \<theta>(t := Some o \<sigma>, t+1 := Some o \<sigma>), def \<turnstile> <cs, \<tau>'(next_time t \<tau>' := 0)> \<leadsto> a"
        by auto
      moreover have ***: "\<forall>s k. k \<le> next_time t \<tau>' \<longrightarrow> signal_of (def s) (\<theta>(t := Some \<circ> \<sigma>, t + 1 := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
      proof (rule+)
        fix s k
        assume "k \<le> next_time t \<tau>'" hence "k \<le> t \<or> k = t + 1 \<or> t + 1 < k" by linarith
        moreover
        { assume "k \<le> t"
          hence "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t+1:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            by (smt add_le_same_cancel1 fun_upd_other not_one_le_zero signal_of_equal_when_trans_equal_upto) }
        moreover 
        { assume "k = t + 1"
          hence "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t +1 := Some o \<sigma>)) s k = \<sigma> s"
            by (meson fun_upd_same trans_some_signal_of)
          also have "... = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            using `\<forall>n\<ge>t. \<theta> n = 0` 
            by (metis (mono_tags, hide_lams) \<open>\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0\<close> \<open>k = t + 1\<close>
            add_diff_cancel_right' fun_upd_same order_refl signal_of_less trans_some_signal_of)
          finally have "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t+1:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            by auto }
        moreover
        { assume "t + 1 < k"
          hence "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t+1 := Some o \<sigma>)) s k = \<sigma> s"
            using `\<forall>n\<ge>t+1. (\<theta>(t:=Some o \<sigma>)) n = 0` 
            by (smt fun_upd_other fun_upd_same less_imp_le_nat nat_neq_iff signal_of_less_ind trans_some_signal_of)
          also have "... = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            using `\<forall>n\<ge>t+1. (\<theta>(t:=Some o \<sigma>)) n = 0` 
            by (smt \<open>t + 1 < k\<close> add_lessD1 discrete fun_upd_same nat_le_linear signal_of_less_ind trans_some_signal_of)
          finally have "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t+1:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
            by auto }
        ultimately show "signal_of (def s) (\<theta>(t:=Some o \<sigma>, t+1:=Some o \<sigma>)) s k = signal_of (def s) (\<theta>(t:=Some o \<sigma>)) s k"
          by auto
      qed
      obtain a' where "maxtime, next_time t \<tau>' , next_state t \<tau>' \<sigma> , next_event t \<tau>' \<sigma> , \<theta>(t := Some \<circ> \<sigma>), def \<turnstile> <cs , \<tau>'(next_time t \<tau>' := 0)> \<leadsto> a'"
        using only_context_matters_b_simulate_fin_progress[OF ** ***]
        by (smt \<open>\<forall>n\<ge>t + 1. (\<theta>(t := Some \<circ> \<sigma>)) n = 0\<close> add_leD1 dual_order.order_iff_strict
        fun_upd_apply leD le_add_diff_inverse next_time_at_least2 not_match)
      then show ?thesis 
        using 1(2) 
        by (metis "1.hyps"(1) \<open>\<not> quiet \<tau> \<gamma> \<and> next_time t \<tau>' \<le> maxtime\<close> add_lessD1 add_to_beh_def b_simulate_fin.intros(1) not_match)
    qed }
  ultimately show ?case
    by auto
next
  case (2 maxtime \<sigma> \<gamma> \<theta> def cs \<tau>)
  then show ?case 
    using b_simulate_fin.intros(4) by blast 
qed *)

abbreviation get_beh'   where "get_beh'   \<equiv> fst o snd o snd"
abbreviation get_trans' where "get_trans' \<equiv> snd o snd o snd"


lemma b_simulate_fin_suc_semi_equivalent:
  assumes   "maxtime, t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<leadsto>s res1"
  assumes   "maxtime, t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<leadsto>s res2"
  assumes   "\<forall>s k. k \<le> t \<longrightarrow> signal_of (def s) \<theta>1 s k = signal_of (def s) \<theta>2 s k"
  assumes   "\<forall>n\<ge>t. \<theta>1 n = 0" and "\<forall>n\<ge>t. \<theta>2 n = 0"  
  shows   "get_state res1 = get_state res2 \<and> get_trans' res1 = get_trans' res2
          \<and> (\<forall>s k. k \<le> maxtime \<longrightarrow> signal_of (def s) (get_beh' res1) s k = signal_of (def s) (get_beh' res2) s k)"
  using assms
proof (induction "maxtime - t" arbitrary: maxtime t \<sigma> \<gamma> \<theta>1 \<theta>2 \<tau>)
  case 0
  then show ?case 
    by (metis (mono_tags, lifting) bau_suc comp_def fst_conv less_asym' snd_conv zero_less_diff)
next
  case (Suc x) hence " x= maxtime - (t + 1)" and "t < maxtime" by auto
  note ex1 = `maxtime, t , \<sigma> , \<gamma> , \<theta>1, def \<turnstile> <cs , \<tau>> \<leadsto>s res1`
  then obtain \<tau>1' where cex1: "t, \<sigma>, \<gamma>, \<theta>1, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>1'" and 
                        ex1': "maxtime, t + 1, next_state2 (t + 1) \<tau>1' \<sigma>, next_event2 (t + 1) \<tau>1' \<sigma>, \<theta>1(t:= Some o \<sigma>), def \<turnstile> <cs, \<tau>1'(t + 1 := 0)> \<leadsto>s res1"
    using bau_suc[OF ex1] `t < maxtime` by auto
  note ex2 = `maxtime, t , \<sigma> , \<gamma> , \<theta>2, def \<turnstile> <cs , \<tau>> \<leadsto>s res2`
  then obtain \<tau>2' where cex2: "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>2'"
    using bau_suc[OF ex2] `t < maxtime` by auto
  hence "t, \<sigma>, \<gamma>, \<theta>2, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>1'" and 
                        ex2': "maxtime, t + 1, next_state2 (t + 1) \<tau>1' \<sigma>, next_event2 (t + 1) \<tau>1' \<sigma>, \<theta>2(t:= Some o \<sigma>), def \<turnstile> <cs, \<tau>1'(t + 1 := 0)> \<leadsto>s res2"
    using bau_suc[OF ex2] `t < maxtime` b_conc_exec_deterministic_weaker[OF cex1 cex2 Suc(5)] apply blast
    using bau_suc[OF ex2] `t < maxtime` b_conc_exec_deterministic_weaker[OF cex1 cex2 Suc(5)]
    by (smt Suc_eq_plus1 b_conc_exec_deterministic cex2 less_irrefl_nat)
  note IH = Suc(1)[OF `x = maxtime - (t + 1)` ex1' ex2']
  have "\<forall>s k. k \<le> t + 1 \<longrightarrow> signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
  proof (rule+)
    fix s k assume "k \<le> t + 1" hence "k < t \<or> k = t \<or> k = t + 1" by linarith
    moreover
    { assume "k < t"
      hence "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k =  signal_of (def s) (\<theta>1) s k"
        by (metis fun_upd_other leD le_refl signal_of_equal_when_trans_equal_upto)
      also have "... = signal_of (def s) (\<theta>2) s k"
        using Suc(5) `k < t` by auto
      also have "... = signal_of (def s) (\<theta>2(t:=Some o \<sigma>)) s k"
        using `k < t`
        by (metis fun_upd_other leD le_refl signal_of_equal_when_trans_equal_upto)
      finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
        by auto }
    moreover
    { assume "k = t"
      hence "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
        by (metis fun_upd_same trans_some_signal_of) }
    moreover
    { assume "k = t + 1"
      hence "signal_of (def s) (\<theta>1(t := Some o \<sigma>)) s k = \<sigma> s"
        using `\<forall>n\<ge>t. \<theta>1 n = 0` 
        by (metis (mono_tags, lifting) add_diff_cancel_right' fun_upd_other fun_upd_same le_add1 signal_of_less trans_some_signal_of)
      also have "... = signal_of (def s) (\<theta>2(t:= Some o \<sigma>)) s k"
        using `\<forall>n\<ge>t. \<theta>2 n = 0` 
        by (metis (mono_tags, lifting) \<open>k = t + 1\<close> add_diff_cancel_right' fun_upd_other fun_upd_same
        le_add1 signal_of_less trans_some_signal_of)
      finally have "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
        by auto }
    ultimately show "signal_of (def s) (\<theta>1(t := Some \<circ> \<sigma>)) s k = signal_of (def s) (\<theta>2(t := Some \<circ> \<sigma>)) s k"
      by auto
  qed
  note IH2 = IH[OF this]
  then show ?case 
    using Suc.prems(4) Suc.prems(5) by fastforce
qed

inductive b_simulate :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trans_raw \<Rightarrow> nat \<times> 'signal state \<times> 'signal event \<times> 'signal trans_raw  \<times> 'signal trans_raw \<Rightarrow> bool"
  where
  "     init' 0 def {} 0 def cs \<tau> \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def = \<gamma>'
   \<Longrightarrow>  maxtime, t', \<sigma>', \<gamma>', 0, def \<turnstile> <cs, \<tau>'(t' := 0)> \<leadsto> res
   \<Longrightarrow>  b_simulate maxtime def cs \<tau> res"

text \<open>Judgement @{term "b_simulate"} contains one rule only: executing the @{term "init'"} rule
before @{term "b_simulate_fin"}.\<close>

inductive_cases bsim : "b_simulate maxtime def cs \<tau> res"

lemma bsimulate_obt_big_step:
  assumes "b_simulate maxtime def cs \<tau> res"
  assumes "init' 0 def {} 0 def cs \<tau> \<tau>'"
  shows "maxtime, next_time  0 \<tau>', next_state 0 \<tau>' def, next_event 0 \<tau>' def,
                             0, def \<turnstile> <cs, \<tau>'(next_time 0 \<tau>' := 0)> \<leadsto> res"
  using bsim[OF assms(1)] assms  by (metis init'_deterministic)

text \<open>Similar to the theorem accompanying @{term "b_simulate_fin"}, i.e.
@{thm "b_simulate_fin_deterministic"}, the rule @{term "b_simulate"} is also deterministic.\<close>

theorem b_sim_init_deterministic:
  assumes "b_simulate maxtime def cs \<tau> res1"
  assumes "b_simulate maxtime def cs \<tau> res2"
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

type_synonym 'signal configuration_raw = "nat \<times> 'signal  state \<times> 'signal event \<times> 'signal trans_raw \<times> 'signal state"

fun update_config_raw :: "'signal configuration_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal configuration_raw"
  where
  "update_config_raw (t, \<sigma>, \<gamma>, \<theta>, def ) \<tau>' = (let t' = next_time t \<tau>';
                                        \<sigma>' = next_state t \<tau>' \<sigma>;
                                        \<gamma>' = next_event t \<tau>' \<sigma>;
                                        \<theta>' = add_to_beh2 \<sigma> \<theta> t def
                                    in (t', \<sigma>', \<gamma>', \<theta>', def))"

inductive b_simulate_fin_ss :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal conc_stmt \<Rightarrow>
  'signal trans_raw \<times> 'signal configuration_raw  \<Rightarrow>  'signal trans_raw \<times> 'signal configuration_raw \<Rightarrow> bool"
  where

  "     t = maxnat 
   \<Longrightarrow>  b_simulate_fin_ss maxnat def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>, maxnat, \<sigma>, \<gamma>, \<theta>, def)"

   \<comment> \<open>The simulation has quiesced and there is still time\<close>
|   "    t < maxnat
   \<Longrightarrow> quiet \<tau> \<gamma>
   \<Longrightarrow> b_simulate_fin_ss maxnat def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>, maxnat, \<sigma>, \<gamma>, \<theta>, def)"

   \<comment> \<open>Business as usual: not quiesced yet and there is still time --- case 1\<close>
| "    t < maxnat
   \<Longrightarrow> \<not> quiet \<tau> \<gamma>
   \<Longrightarrow> t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'
   \<Longrightarrow> next_time t \<tau>' \<le> maxnat
   \<Longrightarrow> update_config_raw (t, \<sigma>, \<gamma>, \<theta>, def) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>', def')
   \<Longrightarrow> b_simulate_fin_ss maxnat def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>'(t':=0), t', \<sigma>', \<gamma>', \<theta>', def')"

   \<comment> \<open>Business as usual: not quiesced yet and there is still time --- case 2\<close>
| "    t < maxnat
   \<Longrightarrow> \<not> quiet \<tau> \<gamma>
   \<Longrightarrow> t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'
   \<Longrightarrow> maxnat < next_time t \<tau>'
   \<Longrightarrow> b_simulate_fin_ss maxnat def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', maxnat, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, def)"

inductive_cases sim_ss_ic : "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"

lemma
  assumes "t < maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>, maxtime, \<sigma>, \<gamma>, res',def')"
  shows "\<theta> = res'"
  using assms sim_ss_ic by blast

lemma
  assumes "t < maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta>, def \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "next_time t \<tau>' < maxtime"
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  shows "update_config_raw (t, \<sigma>, \<gamma>, \<theta>, def) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>', def')"
  apply (rule sim_ss_ic[OF assms(5)])
  using assms(1) apply blast
  using assms(2) apply blast
  apply (metis Pair_inject assms(3) b_conc_exec_deterministic_weaker update_config_raw.simps)
  using assms(4) by linarith

theorem b_simulate_fin_ss_deterministic:
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1, def1)"
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2, def2)"
  shows "(\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1, def1) = (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2, def2)"
  using assms
proof (induction arbitrary: \<tau>2 t2 \<sigma>2 \<gamma>2 \<theta>2 def2 rule: b_simulate_fin_ss.induct)
  case (1 t maxnat def cs \<tau> \<sigma> \<gamma> \<theta>)
  thus ?case 
    by (auto intro!: sim_ss_ic[OF 1(2)])
next
  case (2 t maxnat \<tau> \<gamma> def cs \<sigma> \<theta>)
  then show ?case 
    by (auto intro!: sim_ss_ic[OF 2(3)])
next
  case (3 t maxnat \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>' t' \<sigma>' \<gamma>' \<theta>' def')
  thus ?case 
    by (smt b_conc_exec_deterministic leD nat_neq_iff sim_ss_ic update_config_raw.simps)
next
  case (4 t maxnat \<tau> \<gamma> \<sigma> \<theta> def cs \<tau>')
  thus ?case
    by (smt b_conc_exec_deterministic leD nat_neq_iff sim_ss_ic)
qed

abbreviation
  simulate_ss :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trans_raw \<times> 'signal configuration_raw
                                             \<Rightarrow>  'signal trans_raw \<times> 'signal configuration_raw \<Rightarrow> bool"
  where "simulate_ss maxnat def cs \<rho> \<rho>' \<equiv> star (b_simulate_fin_ss maxnat def cs) \<rho> \<rho>'"

lemma b_simulate_fin_ss_preserve_hist:
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "\<And>n. (min maxtime t)  < n \<Longrightarrow>  \<theta> n = 0"
  assumes "\<And>n. n  < t \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. (min maxtime t') < n \<Longrightarrow>  \<theta>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "min maxtime t' < n" and "t' = maxtime" and "t = maxtime" 
  thus "\<theta>' n = 0"
    using assms(2)
  proof -
    have "\<theta>' = \<theta>"
      using \<open>t = maxtime\<close> assms(1) sim_ss_ic by fastforce
    then show ?thesis
      using \<open>\<And>n. min maxtime t < n \<Longrightarrow> \<theta> n = 0\<close> \<open>min maxtime t' < n\<close> \<open>t = maxtime\<close> \<open>t' = maxtime\<close> by blast
  qed
next
  fix n
  assume "min maxtime t' < n"
  assume "t' = maxtime"
  hence  "maxtime < n"
    using \<open>min maxtime t' < n\<close> by auto
  assume "t < maxtime"
  with assms(2) \<open>maxtime < n\<close> have "\<theta> n = 0"
    by auto
  assume "\<theta>' = \<theta>"
  thus "\<theta>' n = 0"
    using \<open>\<theta> n = 0\<close> \<open>maxtime < n\<close> \<open>t < maxtime\<close> by auto
next
  fix n             
  fix \<tau>'' :: "'a trans_raw"
  assume " min maxtime t' < n"
  assume "next_time t \<tau>'' \<le> maxtime"
  assume "\<tau>' = \<tau>''(next_time t \<tau>'' := 0)" and "t' = next_time t \<tau>'' " and " \<sigma>' = next_state t \<tau>'' \<sigma>" and "\<gamma>' = next_event t \<tau>'' \<sigma>" and "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
  hence *: "\<theta>' = add_to_beh2 \<sigma> \<theta> t def" and "t' = next_time t \<tau>''"
    unfolding Let_def by auto
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>''"
  hence "\<And>n. n < t \<Longrightarrow> \<tau>'' n = 0"
    using b_conc_exec_preserve_trans_removal assms(3) by blast
  hence "t < next_time t \<tau>'' \<or> t = next_time t \<tau>''"
    using next_time_at_least assms(3)  by (simp add: next_time_at_least le_imp_less_or_eq)
  moreover
  { assume "t < next_time t \<tau>''"
    hence "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
      using *  by auto
    hence "\<theta>' n = 0"
      using assms(2) 
      using \<open>min maxtime t' < n\<close> \<open>next_time t \<tau>'' \<le> maxtime\<close> \<open>t < next_time t \<tau>''\<close> \<open>t' = next_time t
      \<tau>''\<close> 
      by (metis (no_types, lifting) add_to_beh2_def dual_order.strict_trans fun_upd_other min_absorb2 min_less_iff_disj order.asym) }
  moreover
  { assume "t = next_time t \<tau>''"
    hence "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
      using * unfolding add_to_beh_def by auto
    hence "\<theta>' n = 0"
      using assms(2) using \<open>min maxtime t' < n\<close> \<open>t = next_time t \<tau>''\<close> \<open>t' = next_time t \<tau>''\<close> 
      using \<open>next_time t \<tau>'' \<le> maxtime\<close> 
      by (smt add_to_beh2_def fun_upd_other min_absorb2 not_le order_refl)}
  ultimately show "\<theta>' n = 0"
    by auto
next
  fix n
  assume "min maxtime t' < n"
  assume "t' = maxtime"
  hence  "maxtime \<le> n"
    using \<open>min maxtime t' < n\<close> by auto
  assume "t < maxtime"
  assume "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
  thus "\<theta>' n = 0"
    using assms(2) \<open>maxtime \<le> n\<close> \<open>t < maxtime\<close> 
    using \<open>min maxtime t' < n\<close> \<open>t' = maxtime\<close>  by (smt add_to_beh2_def fun_upd_other min_less_iff_disj not_le)
qed

lemma small_step_preserve_trans_removal:
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "\<And>n. n < t  \<Longrightarrow>  \<tau> n = 0"
  shows   "\<And>n. n < t' \<Longrightarrow>  \<tau>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "n < t'"
  assume "t' = maxtime"
  assume "t = maxtime"
  assume "\<tau>' = \<tau>"
  thus "\<tau>' n = 0"
    using assms(2) \<open>n < t'\<close> 
    by (simp add: \<open>t = maxtime\<close> \<open>t' = maxtime\<close>)
next
  fix n
  assume "n < t'"
  assume "quiet \<tau> \<gamma>"
  assume "\<tau>' = \<tau>"
  thus  "\<tau>' n = 0"
    using assms(2) \<open>n < t'\<close> \<open>quiet \<tau> \<gamma>\<close> unfolding quiet_def zero_fun_def zero_option_def
    by meson
next
  fix n
  fix \<tau>'' :: "'a trans_raw"
  assume "n < t'"
  assume "t < maxtime"
  assume "\<not> quiet \<tau> \<gamma>"
  assume "next_time t \<tau>'' \<le> maxtime"
  assume "\<tau>' = \<tau>''(next_time t \<tau>'' := 0)" and "t' = next_time t \<tau>'' " and " \<sigma>' = next_state t \<tau>'' \<sigma>" and "\<gamma>' = next_event t \<tau>'' \<sigma>" and "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
  hence  "t' = next_time t \<tau>''" 
    unfolding Let_def by auto
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>''"
  hence  "\<And>n. n < t \<Longrightarrow> \<tau>'' n = 0"
    using b_conc_exec_preserve_trans_removal assms(2)  by blast
  moreover have "t \<le> t'"
    unfolding \<open>t' = next_time t \<tau>''\<close> by (simp add: calculation next_time_at_least)
  ultimately show "\<tau>' n = 0"                                                            
    using \<open>n < t'\<close> \<open>t' = next_time t \<tau>''\<close>  
    by (simp add: \<open>\<tau>' = \<tau>''(next_time t \<tau>'' := 0)\<close> next_time_at_least2)
next
  fix n
  assume "n < t'"
  assume "t' = maxtime"
  assume "maxtime < next_time t \<tau>'"
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  thus "\<tau>' n = 0"
    using assms(2) 
    by (metis \<open>maxtime < next_time t \<tau>'\<close> \<open>n < t'\<close> \<open>t' = maxtime\<close> dual_order.strict_trans next_time_at_least2)
qed

lemma ss_big_continue:  
  assumes "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "b_simulate_fin maxtime t' \<sigma>' \<gamma>' \<theta>' def cs \<tau>' res"
  assumes "\<forall>n. (min maxtime t)  < n \<longrightarrow> \<theta> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> res"
proof (rule sim_ss_ic[OF assms(1)])
  assume "t' = maxtime"
  assume "\<tau>' = \<tau>"
  assume "t = maxtime"
  assume "\<sigma>' = \<sigma>"
  assume "\<gamma>' = \<gamma>"
  assume "\<theta>' = \<theta>"
  thus   "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
    using assms(2) 
    by (simp add: \<open>\<gamma>' = \<gamma>\<close> \<open>\<sigma>' = \<sigma>\<close> \<open>\<tau>' = \<tau>\<close> \<open>t = maxtime\<close> \<open>t' = maxtime\<close>)
next
  assume "t' = maxtime"
  assume "\<sigma>' = \<sigma>" and "\<tau>' = \<tau>" and "\<theta>' = \<theta>"
  assume "quiet \<tau> \<gamma>" and "t < maxtime"
  hence " maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> (maxtime, \<sigma>, \<gamma>, \<theta>, 0)"
    by (metis (no_types, lifting) b_simulate_fin.intros(3) b_simulate_fin.intros(4) order.not_eq_order_implies_strict quiet_def)
  also have "... = res"
    by (smt \<open>quiet \<tau> \<gamma>\<close> assms(1) assms(2) b_simulate_fin.intros(4) b_simulate_fin_deterministic quiet_def sim_ss_ic)
  finally show "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
    by auto
next
  fix \<tau>'' :: "'a trans_raw"
  assume 0: " t < maxtime"
  assume 1: "\<not> quiet \<tau> \<gamma>"
  assume 2: "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>''"
  assume 3: "next_time t \<tau>'' \<le> maxtime"
  assume "\<tau>' = \<tau>''(next_time t \<tau>'' := 0)" and "t' = next_time t \<tau>'' " and " \<sigma>' = next_state t \<tau>'' \<sigma>" and "\<gamma>' = next_event t \<tau>'' \<sigma>" and "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
  hence "t' = next_time t \<tau>''" and "\<sigma>' = next_state t \<tau>'' \<sigma>" and "\<gamma>' = next_event t \<tau>'' \<sigma>" and "\<theta>' =  add_to_beh2 \<sigma> \<theta> t def"
    unfolding Let_def by auto
  thus "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
    using "0" "1" "2" "3" \<open>\<gamma>' = next_event t \<tau>'' \<sigma>\<close> \<open>\<sigma>' = next_state t \<tau>'' \<sigma>\<close> \<open>\<theta>'=  add_to_beh2 \<sigma> \<theta> t def\<close> \<open>t' = next_time t \<tau>''\<close> assms(2) b_simulate_fin.intros(1) 
    using \<open>\<tau>' = \<tau>''(next_time t \<tau>'' := 0)\<close> by blast
next
  assume "t < maxtime"
  assume "\<not> quiet \<tau> \<gamma>"
  assume "t , \<sigma> , \<gamma> , \<theta>, def  \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assume "maxtime < next_time t \<tau>'"
  assume "t' = maxtime"
  assume "\<sigma>' = \<sigma>" and "\<gamma>' = {}" and "\<theta>' = add_to_beh2 \<sigma> \<theta> t def"
  hence "maxtime, maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs, \<tau>'> \<leadsto> res"
    using assms(2)  by (simp add: \<open>t' = maxtime\<close>)
  have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
  moreover
  { assume "\<tau>' = 0"
    hence "quiet \<tau>' {}"
      unfolding quiet_def by auto
    hence "res = (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, 0)"
      using bau[OF \<open>maxtime, maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs, \<tau>'> \<leadsto> res\<close>]  using \<open>\<tau>' = 0\<close> by blast
    hence "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
      using \<open>\<not> quiet \<tau> \<gamma>\<close> \<open>\<tau>' = 0\<close> \<open>maxtime < next_time t \<tau>'\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> \<open>t < maxtime\<close> 
      by (metis Suc_eq_plus1 Suc_leI leD next_time_def) }
  moreover
  { assume "\<tau>' \<noteq> 0"
    hence "\<not> quiet \<tau>' {}"
      unfolding quiet_def by auto
    have "maxtime , \<sigma> , {} , add_to_beh2 \<sigma> \<theta> t def, def  \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'"
      by (simp add: b_conc_exec_empty_event)
    have "res = (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, \<tau>')"
      apply (rule bau[OF \<open>maxtime, maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs, \<tau>'> \<leadsto> res\<close>]) 
      apply (metis \<open>\<tau>' \<noteq> 0\<close> \<open>maxtime , \<sigma> , {} , add_to_beh2 \<sigma> \<theta> t def, def \<turnstile> <cs , \<tau>'> \<longrightarrow>\<^sub>c \<tau>'\<close> \<open>maxtime < next_time t \<tau>'\<close> b_conc_exec_deterministic_weaker leD next_time_def)
      using b_conc_exec_deterministic b_conc_exec_empty_event apply blast
      using \<open>\<not> quiet \<tau>' {}\<close> by blast
    have "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
      by (smt \<open>\<not> quiet \<tau> \<gamma>\<close> \<open>\<theta>' = add_to_beh2 \<sigma> \<theta> t def\<close> \<open>maxtime < next_time t \<tau>'\<close> \<open>res = (maxtime, \<sigma>, {}, add_to_beh2 \<sigma> \<theta> t def, \<tau>')\<close> \<open>t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<longrightarrow>\<^sub>c \<tau>'\<close> \<open>t < maxtime\<close> assms(1) b_simulate_fin.intros(2) nat_neq_iff sim_ss_ic) }
  ultimately show "maxtime, t , \<sigma> , \<gamma> , \<theta>, def \<turnstile> <cs , \<tau>> \<leadsto> res"
    by auto
qed

theorem small_step_implies_big_step:
  assumes "simulate_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')"
  assumes "\<forall>n. (min maxtime t) < n \<longrightarrow>  \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> \<tau> n = 0"
  assumes "maxtime = t'"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> def cs \<tau> (t', \<sigma>', \<gamma>', \<theta>', \<tau>')"
  using assms
proof (induction "(\<tau>, t, \<sigma>, \<gamma>, \<theta>, def)" "(\<tau>', t', \<sigma>', \<gamma>', \<theta>', def')" arbitrary: \<tau> t \<sigma> \<gamma> \<theta>  rule: star.induct)
  case refl
  then show ?case
    by (simp add: b_simulate_fin.intros(4))
next
  case (step y)
  obtain \<tau>'' t'' \<sigma>'' \<gamma>'' \<theta>'' def'' where y_def: "y = (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'', def'')"
    using prod_cases6 by blast
  hence *: "b_simulate_fin_ss maxtime def cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>, def) (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'', def'')"
    using step(1) by blast
  hence "def'' = def"
    using sim_ss_ic by blast
  hence y_def': "y = (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'', def)"
    unfolding y_def by auto
  have **: "\<forall>n> (min maxtime t'').  \<theta>'' n = 0"
    using b_simulate_fin_ss_preserve_hist[OF *] step.prems by auto
  have ***: "\<forall>n<t''.  \<tau>'' n = 0"
    using "*" small_step_preserve_trans_removal step.prems(2) by blast
  show ?case
    using ss_big_continue[OF * step(3)[OF y_def' ** ***] step(4)]  \<open>maxtime  = t'\<close>
    by auto
qed

end