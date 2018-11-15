(*
 * Copyright 2018, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 *  Author: Albert Rizaldi, NTU Singapore
 *)

theory Femto_VHDL
  imports Main
          "Polynomials.Poly_Mapping"
          "HOL-Library.Infinite_Set"
          "HOL-Library.Finite_Map"
          "HOL-IMP.Star"
          "Polynomials.Poly_Mapping_Finite_Map"
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

(* TODO: replace proof by smt *)
lemma upd_eventually_cofinite:
  assumes  "\<forall>\<^sub>\<infinity>n. f n = 0"
  shows "\<forall>\<^sub>\<infinity>n. (f(m := k)) n = 0"
  using assms
  by (smt MOST_neq(2) eventually_elim2 fun_upd_def)

lift_definition override_lookups_on_open_right ::
                 "(nat, 'a ::zero) poly_mapping \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a ::zero) poly_mapping"
  is "\<lambda>p v lo hi. override_on p (\<lambda>n. v) {lo ..< hi}"
proof -
  fix a :: "'a"
  fix n1 n2 :: nat
  fix f :: "nat \<Rightarrow> 'a"
  assume "finite {x. f x \<noteq> 0}"
  have "{x. override_on f (\<lambda>n. a) {n1..< n2} x \<noteq> 0} =
        {x. x \<in> {n1 ..< n2} \<and> override_on f (\<lambda>n. a) {n1..< n2} x \<noteq> 0} \<union>
        {x. x \<notin> {n1 ..< n2} \<and> override_on f (\<lambda>n. a) {n1..< n2} x \<noteq> 0}" (is "?set = ?set1 \<union> ?set2")
    by auto
  have "finite ?set1"
    using subset_eq_atLeast0_atMost_finite by auto
  have "?set2 \<subseteq> {x. f x \<noteq> 0}"
    unfolding override_on_def by auto
  hence "finite ?set2"
    using \<open>finite {x. f x \<noteq> 0}\<close>  using finite_subset by blast
  thus "finite ?set"
    using `finite ?set1` `?set = ?set1 \<union> ?set2`  by (metis (no_types, lifting) finite_UnI)
qed

lemma override_coeffs_open_right_same_idx:
  "override_lookups_on_open_right p v lo lo = p"
  by (transfer, auto)

lift_definition override_lookups_on_closed ::
                        "(nat, 'a ::zero) poly_mapping \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) poly_mapping"
  is "\<lambda>p v lo hi. override_on p (\<lambda>n. v) {lo .. hi}"
proof -
  fix a :: "'a"
  fix n1 n2 :: nat
  fix f :: "nat \<Rightarrow> 'a"
  assume "finite {x. f x \<noteq> 0}"
  have "{x. override_on f (\<lambda>n. a) {n1.. n2} x \<noteq> 0} =
        {x. x \<in> {n1 .. n2} \<and> override_on f (\<lambda>n. a) {n1.. n2} x \<noteq> 0} \<union>
        {x. x \<notin> {n1 .. n2} \<and> override_on f (\<lambda>n. a) {n1.. n2} x \<noteq> 0}" (is "?set = ?set1 \<union> ?set2")
    by auto
  have "finite ?set1"
    using subset_eq_atLeast0_atMost_finite by auto
  have "?set2 \<subseteq> {x. f x \<noteq> 0}"
    unfolding override_on_def by auto
  hence "finite ?set2"
    using \<open>finite {x. f x \<noteq> 0}\<close>  using finite_subset by blast
  thus "finite ?set"
    using `finite ?set1` `?set = ?set1 \<union> ?set2`  by (metis (no_types, lifting) finite_UnI)
qed

lemma override_lookups_closed_same_endpoints:
  assumes "override_lookups_on_closed m v t t = m'"
  shows "m' = Poly_Mapping.update t v m"
  using assms
  by (transfer)(auto simp add: override_on_def)

lift_definition override_lookups_on_open_left ::
                        "(nat, 'a ::zero) poly_mapping \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) poly_mapping"
  is "\<lambda>p v lo hi. override_on p (\<lambda>n. v) {lo <.. hi}"
proof -
  fix a :: "'a"
  fix n1 n2 :: nat
  fix f :: "nat \<Rightarrow> 'a"
  assume "finite {x. f x \<noteq> 0}"
  have "{x. override_on f (\<lambda>n. a) {n1 <.. n2} x \<noteq> 0} =
        {x. x \<in> {n1 <.. n2} \<and> override_on f (\<lambda>n. a) {n1 <.. n2} x \<noteq> 0} \<union>
        {x. x \<notin> {n1 <.. n2} \<and> override_on f (\<lambda>n. a) {n1 <.. n2} x \<noteq> 0}" (is "?set = ?set1 \<union> ?set2")
    by auto
  have "finite ?set1"
    using subset_eq_atLeast0_atMost_finite by auto
  have "?set2 \<subseteq> {x. f x \<noteq> 0}"
    unfolding override_on_def by auto
  hence "finite ?set2"
    using \<open>finite {x. f x \<noteq> 0}\<close>  using finite_subset by blast
  thus "finite ?set"
    using `finite ?set1` `?set = ?set1 \<union> ?set2`  by (metis (no_types, lifting) finite_UnI)
qed

lemma [code]:
  "override_lookups_on_closed m v lo hi = override_lookups_on_open_right m v lo (hi + 1)"
  by (transfer) (auto simp add: atLeastLessThanSuc_atLeastAtMost)

lemma [code]:
  "override_lookups_on_open_left m v lo (Suc hi) =
                                                override_lookups_on_open_right m v (lo + 1) (hi + 2)"
  by (transfer', auto simp add: atLeastLessThanSuc_atLeastAtMost atLeastSucAtMost_greaterThanAtMost)

lemma [code]:
  "override_lookups_on_open_left m v lo 0 = m"
  by (transfer', auto)

lemma override_lookups_on_open_left_hi_lo:
  "lo \<le> hi \<Longrightarrow> override_lookups_on_open_left m l hi lo = m"
  by transfer' (auto simp add:override_on_def)

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
    | Bsingle "'signal set" "'signal seq_stmt" (" process _ : _" [81, 82]80)

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

subsection "Operational Semantics"

type_synonym time = nat
type_synonym val = bool
type_synonym 'signal event = "'signal set"
type_synonym 'signal state = "'signal \<Rightarrow> val"

abbreviation def_state :: "'signal state" where
  "def_state \<equiv> (\<lambda>s. False)"

(* TODO: change this to fmap *)
type_synonym 'signal valuation = "'signal \<rightharpoonup> val"

\<comment> \<open> represents scheduling \<close>
type_synonym 'signal trans_raw = "nat \<Rightarrow> 'signal valuation"
type_synonym 'signal transaction = "(nat, 'signal valuation) poly_mapping"

abbreviation get_trans :: "'signal transaction \<Rightarrow> time \<Rightarrow> 'signal \<rightharpoonup> val" where
  "get_trans \<tau> n \<equiv> Poly_Mapping.lookup \<tau> n"

abbreviation empty_trans :: "'signal transaction" where
  "empty_trans \<equiv> 0"

type_synonym 'signal trace = "(nat, 'signal valuation) poly_mapping"

subsection \<open>New reprsentation of transaction \<close>

(* TODO : introductory text for this subsection*)

type_synonym 'signal trans_raw2 = "'signal \<Rightarrow> nat \<Rightarrow> val option"
type_synonym 'signal transaction2 = "'signal \<Rightarrow> nat \<Rightarrow>\<^sub>0 val option"

definition to_trans_raw2 :: "'signal trans_raw \<Rightarrow> 'signal trans_raw2" where
  "to_trans_raw2 \<tau> = (\<lambda>sig n. \<tau> n sig)"

lift_definition to_transaction2 :: "'signal transaction \<Rightarrow> 'signal transaction2" is to_trans_raw2
  by (metis (mono_tags, lifting) finite_subset mem_Collect_eq subsetI to_trans_raw2_def zero_fun_def)

subsection \<open>From transaction to function of time (signal)\<close>

fun inf_key :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "inf_key ks n = (case takeWhile (\<lambda>k. k \<le> n) ks of [] \<Rightarrow> None | ks' \<Rightarrow> Some (last ks'))"

lemma inf_keyE1:
  assumes "inf_key ks n = Some k"
  obtains ks' where "takeWhile (\<lambda>k. k \<le> n) ks = ks'" and "last ks' = k"
  using assms by (auto split:list.splits)

lemma inf_key_in_list:
  assumes "inf_key ks n = Some k"
  shows "k \<in> set ks"
proof -
  obtain ks' where "takeWhile (\<lambda>k. k \<le> n) ks = ks'"  and "last ks' = k" and "ks' \<noteq> []"
    using assms by (auto split:list.splits)
  hence "set ks' \<subseteq> set ks"
    by (meson set_takeWhileD subsetI)
  moreover have "k \<in> set ks'"
    using `last ks' = k` last_in_set `ks' \<noteq> []` by auto
  ultimately show ?thesis
    by auto
qed

lemma inf_key_tail:
  assumes "sorted (a # ks)"
  assumes "inf_key ks n = Some x"
  assumes "inf_key (a # ks) n = Some y"
  shows "x = y"
proof -
  obtain ks' where *: "takeWhile (\<lambda>k. k \<le> n) ks = ks'" and "ks' \<noteq> []" and "last ks' = x"
    using assms(2) inf_keyE1 by fastforce
  have "takeWhile (\<lambda>k. k \<le> n) (a # ks) = a # ks'"
    by (metis * assms(3) inf_key.simps list.simps(4) option.simps(3) takeWhile.simps(2))
  moreover hence "last (a # ks') = x"
    using `last ks' = x` `ks' \<noteq> []` by auto
  ultimately have "inf_key (a # ks) n = Some x"
    by auto
  thus ?thesis using assms by auto
qed

lemma inf_key_none:
  assumes "sorted ks"
  shows "inf_key ks n = None \<Longrightarrow> \<forall>k \<in> set ks. n < k"
  using assms
  by (induction ks)(auto split:if_splits)

lemma inf_key_correct:
  assumes "sorted ks"
  assumes "inf_key ks n = Some k'"
  shows "\<forall>k \<in> set ks. k \<le> n \<longrightarrow> k \<le> k'"
  using assms
proof (induction ks)
  case Nil
  then show ?case by auto
next
  case (Cons a ks)
  show ?case
  proof (intro ballI)
    fix k
    assume "k \<in> set (a # ks)"
    hence "k = a \<or> k \<in> set ks" by auto
    moreover
    { assume "k = a"
      have "k' = a \<or> k' \<in> set ks"
        using Cons(3) by (meson inf_key_in_list set_ConsD)
      moreover have "k' = a \<Longrightarrow> k \<le> k'"
        using `k = a` by auto
      moreover have "k' \<in> set ks \<Longrightarrow> k \<le> k'"
        using Cons(2) `k = a` by auto
      ultimately have " k \<le> n \<longrightarrow> k \<le> k'" by auto }
    moreover
    { assume "k \<in> set ks"
      have "sorted ks"
        using Cons(2) by auto
      obtain x where  "inf_key ks n = None \<or> inf_key ks n = Some x"
        by (meson option.exhaust)
      moreover
      { assume "inf_key ks n = None"
        hence "\<forall>k \<in> set ks. n < k"
          using inf_key_none[OF `sorted ks`] by auto
        hence "k \<le> n \<longrightarrow> k \<le> k'"
          using `k \<in> set ks` by auto }
      moreover
      { assume *: "inf_key ks n = Some x"
        with Cons(3) have "x = k'"
          using inf_key_tail[OF `sorted (a # ks)`] by metis
        with Cons(1)[OF `sorted ks`] * `k \<in> set ks` have "k \<le> n \<longrightarrow> k \<le> k'"
          by auto }
      ultimately have "k \<le> n \<longrightarrow> k \<le> k'"
        by auto }
    ultimately show "k \<le> n \<longrightarrow> k \<le> k'"
      by auto
  qed
qed

lemma set_keys_dom_lookup:
  fixes \<tau> :: "'signal \<Rightarrow> nat \<Rightarrow>\<^sub>0 'b option"
  fixes sig :: "'signal"
  shows "set (sorted_list_of_set (keys (\<tau> sig))) = dom (lookup (\<tau> sig))"
proof transfer
  fix \<tau> :: "'a \<Rightarrow> nat \<Rightarrow> 'b option"
  fix sig :: "'a"
  assume "pred_fun top (\<lambda>f. finite {x. f x \<noteq> 0}) \<tau>"
  hence "finite {k. \<tau> sig k \<noteq> 0}"
    by auto
  hence "set (sorted_list_of_set {k. \<tau> sig k \<noteq> 0}) = {k. \<tau> sig k \<noteq> None}"
    unfolding zero_option_def by auto
  also have "... = dom (\<tau> sig)"
    unfolding dom_def by auto
  finally show "set (sorted_list_of_set {k. \<tau> sig k \<noteq> 0}) = dom (\<tau> sig)"
    by auto
qed

definition "inf_time \<tau> sig n = inf_key (sorted_list_of_set (keys (\<tau> sig))) n"

lemma
  assumes "inf_time \<tau> sig n = Some k"
  shows "\<forall>t \<in> dom (lookup (\<tau> sig)). t \<le> n \<longrightarrow> t \<le> k"
proof -
  have"inf_key (sorted_list_of_set (keys (\<tau> sig))) n = Some k"
    using assms unfolding inf_time_def by fastforce
  with inf_key_correct have "\<forall>t\<in>set (sorted_list_of_set (keys (\<tau> sig))). t \<le> n \<longrightarrow> t \<le> k"
    using sorted_sorted_list_of_set by blast
  then show ?thesis
    using set_keys_dom_lookup by metis
qed

lemma
  assumes "inf_time \<tau> sig n = None"
  shows "\<forall>t \<in> dom (lookup (\<tau> sig)). n < t"
proof -
  have "inf_key (sorted_list_of_set (keys (\<tau> sig))) n = None"
    using assms unfolding inf_time_def by fastforce
  with inf_key_none have " \<forall>k\<in>set (sorted_list_of_set (keys (\<tau> sig))). n < k"
    using sorted_sorted_list_of_set by blast
  moreover have "set (sorted_list_of_set (keys (\<tau> sig))) = dom (lookup (\<tau> sig))"
    using set_keys_dom_lookup by metis
  ultimately show ?thesis
    using not_le by auto
qed

(* Rethink this definition; should @{term "None \<Rightarrow> False"} be removed ? By introducing new type? lifting? *)
definition to_signal :: "'signal transaction2 \<Rightarrow> 'signal \<Rightarrow> time \<Rightarrow> val" where
  "to_signal \<tau> sig t = (case inf_time \<tau> sig t of
                           None    \<Rightarrow> False
                         | Some t' \<Rightarrow> the (lookup (\<tau> sig) t'))"

abbreviation "signal_of \<equiv> to_signal o to_transaction2"

subsection "Rule of semantics"

subsubsection \<open>Semantics of @{typ "'signal bexp"}\<close>

fun xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<longleftrightarrow> (x \<or> y) \<and> (x \<noteq> y)"

text \<open>The semantics of expression is standard. A slightly more involved denotation is for
@{term "Bsig_delayed"}. Basically, it gets the value in the history @{term "snd \<theta> :: 'signal trace"}
at time @{term "now - t"} where @{term "t"} is the delay.\<close>

fun beval :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow> 'signal bexp \<Rightarrow> val"
  where
  "beval now \<sigma> \<gamma> \<theta> (Bsig sig) = \<sigma> sig"
| "beval now \<sigma> \<gamma> \<theta> (Btrue) = True"
| "beval now \<sigma> \<gamma> \<theta> (Bfalse) = False"
| "beval now \<sigma> \<gamma> \<theta> (Bsig_delayed sig t) = signal_of \<theta> sig (now - t)"
| "beval now \<sigma> \<gamma> \<theta> (Bsig_event sig) = (sig \<in> \<gamma>)"
| "beval now \<sigma> \<gamma> \<theta> (Bnot e) \<longleftrightarrow> \<not> beval now \<sigma> \<gamma> \<theta> e"
| "beval now \<sigma> \<gamma> \<theta> (Band e1 e2) \<longleftrightarrow> beval now \<sigma> \<gamma> \<theta> e1 \<and> beval now \<sigma> \<gamma> \<theta> e2"
| "beval now \<sigma> \<gamma> \<theta> (Bor e1 e2) \<longleftrightarrow> beval now \<sigma> \<gamma> \<theta> e1 \<or> beval now \<sigma> \<gamma> \<theta> e2"
| "beval now \<sigma> \<gamma> \<theta> (Bnand e1 e2) \<longleftrightarrow> \<not> (beval now \<sigma> \<gamma> \<theta> e1 \<and> beval now \<sigma> \<gamma> \<theta> e2)"
| "beval now \<sigma> \<gamma> \<theta> (Bnor e1 e2) \<longleftrightarrow> \<not> (beval now \<sigma> \<gamma> \<theta> e1 \<or> beval now \<sigma> \<gamma> \<theta> e2)"
| "beval now \<sigma> \<gamma> \<theta> (Bxor e1 e2) \<longleftrightarrow> xor (beval now \<sigma> \<gamma> \<theta> e1) (beval now \<sigma> \<gamma> \<theta> e2)"
| "beval now \<sigma> \<gamma> \<theta> (Bxnor e1 e2) \<longleftrightarrow> \<not> xor (beval now \<sigma> \<gamma> \<theta> e1) (beval now \<sigma> \<gamma> \<theta> e2)"

term "to_signal o to_transaction2 "

abbreviation beval_abb :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace
                                                                      \<Rightarrow> 'signal bexp \<Rightarrow> val \<Rightarrow> bool"
 ("_ , _ , _ , _ \<turnstile> _ \<longrightarrow>\<^sub>b _") where
  "now, \<sigma>, \<gamma>, \<theta> \<turnstile> e \<longrightarrow>\<^sub>b val \<equiv> beval now \<sigma> \<gamma> \<theta> e = val"

subsubsection \<open>Semantics of @{typ "'signal seq_stmt"}\<close>

text \<open>The semantics for @{term "Bcomp"} @{term "Bnull"} and @{term "Bguarded"} is very
straightforward, but not so for @{term "Bassign_trans"} and @{term "Bassign_inert"}. The previous
one relies on the following function of @{term "trans_post"} which has the meaning of posting a
transaction (as is database transaction). The latter needs additional function of @{term "purge"}
which eliminates signal spikes before it posts a transaction. Jump (or search more precisely) for
@{term "b_seq_exec"} immediately for the semantics of sequential statements.\<close>

definition trans_post_raw :: "'signal \<Rightarrow> val \<Rightarrow> 'signal trans_raw \<Rightarrow> time \<Rightarrow> 'signal trans_raw"
  where
  "trans_post_raw sig v \<tau> t = (\<lambda>t'. if t' = t    then (\<tau> t') (sig := Some v) else
                                    if t' > t    then (\<tau> t') (sig := None) else
                                    (* t' < t *) \<tau> t')"

(* TODO: remove proof by smt *)
lift_definition trans_post :: "'signal \<Rightarrow> val \<Rightarrow> 'signal transaction \<Rightarrow> time \<Rightarrow> 'signal transaction"
  is trans_post_raw unfolding trans_post_raw_def sym[OF eventually_cofinite]
  by (smt MOST_mono MOST_neq(2) MOST_rev_mp fun_upd_idem_iff zero_fun_def zero_option_def)

fun check :: "('signal \<rightharpoonup> val) \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool" where
  "check \<sigma> sig val = (case \<sigma> sig of None \<Rightarrow> True | Some val' \<Rightarrow> val = val')"

fun is_stable_raw :: "delay \<Rightarrow> (nat \<Rightarrow> 'signal \<rightharpoonup> bool) \<Rightarrow> time \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool" where
  "is_stable_raw 0 _ _ _ _ \<longleftrightarrow> True"
| "is_stable_raw (Suc n) \<tau> now sig val \<longleftrightarrow>
                                     check (\<tau> (now + Suc n)) sig val \<and> is_stable_raw n \<tau> now sig val"

lift_definition is_stable :: "delay \<Rightarrow> 'signal transaction \<Rightarrow> time \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> bool"
  is is_stable_raw .

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

lemma is_stable_correct_only_if:
  "is_stable dly \<tau> now sig val \<Longrightarrow> \<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (get_trans \<tau> m) sig val"
  by (transfer, metis is_stable_raw_correct_only_if)

lemma is_stable_raw_correct_if:
  assumes "\<And>m. now < m \<and> m \<le> now + dly \<Longrightarrow> check (\<tau> m) sig val"
  shows "is_stable_raw dly \<tau> now sig val"
  using assms
  by (induction dly) auto

lemma is_stable_correct_if:
  assumes "\<And>m. now < m \<and> m \<le> now + dly \<Longrightarrow> check (get_trans \<tau> m) sig val"
  shows "is_stable dly \<tau> now sig val"
  using assms
  by (transfer, metis is_stable_raw_correct_if)

lemma is_stable_raw_correct:
  "is_stable_raw dly \<tau> now sig val \<longleftrightarrow> (\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (\<tau> m) sig val)"
  using is_stable_raw_correct_if is_stable_raw_correct_only_if by metis

lemma is_stable_correct:
  "is_stable dly \<tau> now sig val \<longleftrightarrow> (\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (get_trans \<tau> m) sig val)"
  using is_stable_correct_if is_stable_correct_only_if by metis

fun purge_raw :: "delay \<Rightarrow> 'signal trans_raw \<Rightarrow> time \<Rightarrow> 'signal \<Rightarrow> val \<Rightarrow> 'signal trans_raw" where
  "purge_raw 0 \<tau> _ _ _= \<tau>"
| "purge_raw (Suc n) \<tau> now sig val =
             (let f  = \<tau> (now + Suc n);
                  f' = f (sig := None);
                  \<tau>' = \<tau> (now + Suc n := f')
              in
                 if f sig = Some val then purge_raw n \<tau> now sig val else purge_raw n \<tau>' now sig val)"

lift_definition purge :: "delay \<Rightarrow> 'signal transaction \<Rightarrow> time \<Rightarrow> 'signal \<Rightarrow> val
                                                                              \<Rightarrow> 'signal transaction"
  is purge_raw unfolding sym[OF eventually_cofinite]
proof -
  fix f :: "nat \<Rightarrow> 'signal \<rightharpoonup> bool"
  fix nat1 nat2 signal bool
  assume *: " \<forall>\<^sub>\<infinity>n. f n = 0"
  thus "\<forall>\<^sub>\<infinity>n. purge_raw nat1 f nat2 signal bool n = 0"
  proof (induction nat1 arbitrary:f)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
      using upd_eventually_cofinite[OF Suc(2)] by (auto simp add:Let_def)
  qed
qed

lemma purge_raw_induct:
  "\<And>m. now + Suc n \<le> m \<Longrightarrow> purge_raw n \<tau> now sig val m = \<tau> m"
proof (induction n arbitrary:\<tau>)
  case 0
  then show ?case by auto
next
  case (Suc n)
  define f where "f \<equiv> \<tau> (now + Suc n)"
  define f' where "f' \<equiv> f (sig := None)"
  define \<tau>' where "\<tau>' \<equiv> \<tau> (now + Suc n := f')"
  have *: "now + Suc n \<le> m" using Suc by auto
  have "\<tau>' m = \<tau> m"
    using Suc(2) unfolding \<tau>'_def by (auto simp add:field_simps)
  have "f sig = Some val \<or> f sig \<noteq> Some val"
    by auto
  moreover
  { assume "f sig = Some val"
    hence **: "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau> now sig val"
      using purge_raw.simps(2)[of "n" "\<tau>" "now" "sig" "val"]  unfolding Let_def f_def  by auto
    hence ?case using Suc(1)[OF *] **
      by auto }
  moreover
  { assume "f sig \<noteq> Some val"
    hence **: "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau>' now sig val"
      using purge_raw.simps(2)[of "n" "\<tau>" "now" "sig" "val"] unfolding Let_def \<tau>'_def f'_def f_def
      by auto
    hence ?case using Suc(1)[OF *] \<open>\<tau>' m = \<tau> m\<close>
      by auto }
  ultimately show ?case by auto
qed

lemma purge_induct:
  "\<And>m. now + Suc n \<le> m \<Longrightarrow> get_trans (purge n \<tau> now sig val) m = get_trans \<tau> m"
  by (transfer, metis purge_raw_induct)

lemma purge_raw_induct':
  "purge_raw n \<tau> now sig val = \<tau>' \<Longrightarrow>  \<tau>' (now + Suc n) = \<tau> (now + Suc n)"
  using purge_raw_induct[of "now" "n" "now + Suc n" "\<tau>"] by auto

lemma purge_induct':
  "purge n \<tau> now sig val = \<tau>' \<Longrightarrow>  get_trans \<tau>' (now + Suc n) = get_trans \<tau> (now + Suc n)"
  using purge_induct[of "now" "n" "now + Suc n" "\<tau>"] by auto

lemma purge_raw_correctness':
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> \<tau>' m sig = None \<or> \<tau>' m sig = Some val"
  apply (rule allI, rule impI)
  using assms
proof (induction n arbitrary:\<tau> \<tau>')
  case 0
  then show ?case by auto
next
  case (Suc n)
  define f where "f \<equiv> \<tau> (now + Suc n)"
  define f' where "f' \<equiv> f (sig := None)"
  have "f sig = Some val \<or> f sig \<noteq> Some val"
    by auto
  moreover
  { assume "f sig \<noteq> Some val"
    hence **: "purge_raw (Suc n) \<tau> now sig val = purge_raw n (\<tau> (now + Suc n := f')) now sig val"
      unfolding  f_def f'_def by auto
    hence *: "purge_raw n (\<tau> (now + Suc n := f')) now sig val = \<tau>'"
      using Suc by auto
    hence ?case
      by (metis Suc(1) Suc(2) add_Suc_right f'_def fun_upd_same leD less_Suc_eq less_linear
          less_or_eq_imp_le purge_raw_induct) }
  moreover
  { assume "f sig = Some val"
    hence **: "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau> now sig val"
      unfolding f_def f'_def by auto
    hence *: "purge_raw n \<tau> now sig val = \<tau>'"
      using Suc by auto
    hence ?case
      by (metis Suc add_Suc_right calculation(2) f_def less_linear not_le not_less_eq
          purge_raw_induct) }
  ultimately show ?case by auto
qed

lemma purge_correctness':
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> get_trans \<tau>' m sig = None \<or> get_trans \<tau>' m sig = Some val"
  using assms by (transfer, metis purge_raw_correctness')

lemma purge_raw_before_now_unchanged:
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. m \<le> now \<longrightarrow> \<tau> m = \<tau>' m"
  apply (rule allI, rule impI)
  using assms
proof (induction n arbitrary:\<tau> \<tau>')
  case 0
  then show ?case by auto
next
  case (Suc n)
  define f where "f \<equiv> \<tau> (now + Suc n)"
  define f' where "f' \<equiv> f (sig := None)"
  have "f sig = Some val \<or> f sig \<noteq> Some val"
    by auto
  moreover
  { assume "f sig = Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau> now sig val"
      unfolding f_def by auto
    hence "... = \<tau>'" using Suc by auto
    with Suc have ?case by metis }
  moreover
  { assume "f sig \<noteq> Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n (\<tau> (now + Suc n := f')) now sig val"
      unfolding f_def f'_def by auto
    hence "... = \<tau>'" using Suc by auto
    hence "\<tau>' m = (\<tau>(now + Suc n := f')) m " using Suc(1)[OF Suc(2)]  by metis
    also have "... = \<tau> m" using Suc(2) by auto
    finally have ?case  by auto }
  ultimately show ?case by auto
qed

lemma purge_before_now_unchanged:
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. m \<le> now \<longrightarrow> get_trans \<tau> m = get_trans \<tau>' m"
  using assms by (transfer, metis purge_raw_before_now_unchanged)

lemma purge_raw_after_delay_unchanged:
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now + n < m \<longrightarrow> \<tau> m = \<tau>' m"
  apply (rule allI, rule impI)
  using assms
proof (induction n arbitrary: \<tau> \<tau>')
  case 0
  then show ?case by auto
next
  case (Suc n)
  define f where "f \<equiv> \<tau> (now + Suc n)"
  define f' where "f' \<equiv> f (sig := None)"
  have "f sig = Some val \<or> f sig \<noteq> Some val"
    by auto
  moreover
  { assume "f sig = Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau> now sig val"
      unfolding f_def by auto
    hence *: "... = \<tau>'" using Suc by metis
    have "now + n < m" using \<open>now + Suc n < m\<close> by (auto simp add:field_simps)
    have ?case using Suc(1)[OF `now + n < m`] * by metis }
  moreover
  { assume "f sig \<noteq> Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n (\<tau> (now + Suc n := f')) now sig val"
      unfolding f_def f'_def by auto
    hence *: "... = \<tau>'" using Suc by metis
    have "now + n < m" using \<open>now + Suc n < m\<close> by (auto simp add:field_simps)
    hence "\<tau>' m = (\<tau>(now + Suc n := f')) m "
      using Suc(1) * by metis
    also have "... = \<tau> m"  using `now + Suc n < m` by auto
    finally have ?case by auto }
  ultimately show ?case by auto
qed

lemma purge_after_delay_unchanged:
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now + n < m \<longrightarrow> get_trans \<tau> m = get_trans \<tau>' m"
  using assms by (transfer, metis purge_raw_after_delay_unchanged)

lemma purge_raw_does_not_affect_other_sig:
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "\<forall>m s. s \<noteq> sig \<longrightarrow> \<tau>' m s = \<tau> m s"
  apply rule+
  using assms
proof (induction n arbitrary: \<tau> \<tau>')
  case 0
  then show ?case by auto
next
  case (Suc n)
  define f where "f \<equiv> \<tau> (now + Suc n)"
  define f' where "f' \<equiv> f (sig := None)"
  have "f sig = Some val \<or> f sig \<noteq> Some val"
    by auto
  moreover
  { assume "f sig = Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n \<tau> now sig val"
      unfolding f_def by auto
    with Suc have ?case by metis }
  moreover
  { assume "f sig \<noteq> Some val"
    hence "purge_raw (Suc n) \<tau> now sig val = purge_raw n (\<tau> (now + Suc n := f')) now sig val"
      unfolding f_def f'_def by auto
    hence *: "... = \<tau>'" using Suc by metis
    with Suc have "(\<tau>(now + Suc n := f')) m s = \<tau>' m s"
      by metis
    hence ?case
      using `s \<noteq> sig` unfolding f'_def f_def  by (metis fun_upd_apply) }
  ultimately show ?case by auto
qed

lemma purge_does_not_affect_other_sig:
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "\<forall>m s. s \<noteq> sig \<longrightarrow> get_trans \<tau>' m s = get_trans \<tau> m s"
  using assms by (transfer,  metis purge_raw_does_not_affect_other_sig)

lemma purge_raw_correctness:
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> check (\<tau>' m) sig val"
proof -
  have "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> \<tau>' m sig = None \<or> \<tau>' m sig = Some val"
    using purge_raw_correctness'[OF assms] by auto
  thus ?thesis
    by auto
qed

lemma purge_correctness:
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "\<forall>m. now < m \<and> m \<le> now + n \<longrightarrow> check (get_trans \<tau>' m) sig val"
  using assms by (transfer, metis purge_raw_correctness)

lemma stable_raw_after_purge_raw:
  assumes "purge_raw n \<tau> now sig val = \<tau>'"
  shows "is_stable_raw n \<tau>' now sig val"
  using purge_raw_correctness is_stable_raw_correct assms by fastforce

lemma stable_after_purge:
  assumes "purge n \<tau> now sig val = \<tau>'"
  shows "is_stable n \<tau>' now sig val"
  using assms by (transfer, metis stable_raw_after_purge_raw)

text \<open>This is the function for posting a transaction in an inertial assignment statement.\<close>

definition inr_post :: "'signal \<Rightarrow> val \<Rightarrow> val \<Rightarrow> 'signal transaction \<Rightarrow> time \<Rightarrow> delay
                                                                             \<Rightarrow> 'signal transaction"
  where
  "inr_post sig val cur_val \<tau> now dly =
   (if is_stable dly \<tau> now sig cur_val then
      trans_post sig val \<tau> (now + dly)
    else
      trans_post sig val (purge dly \<tau> now sig cur_val) (now + dly))"

fun b_seq_exec :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                               'signal seq_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  where
  "b_seq_exec t \<sigma> \<gamma> \<theta> Bnull \<tau> = \<tau>"
| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau> =
                                    (let \<tau>' = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau> in b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>')"
| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded guard ss1 ss2) \<tau> =
                (if beval t \<sigma> \<gamma> \<theta> guard then b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau> else b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>)"
| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_trans sig e dly) \<tau> =
                                         (let x = (beval t \<sigma> \<gamma> \<theta> e) in trans_post sig x \<tau> (t + dly))"
| "b_seq_exec t \<sigma> \<gamma> \<theta> (Bassign_inert sig e dly) \<tau> =
                                       (let x = (beval t \<sigma> \<gamma> \<theta> e) in inr_post sig x (\<sigma> sig) \<tau> t dly)"

abbreviation b_seq_exec_abb :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                               'signal seq_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool"
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

lift_definition map_diff_trans :: "'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  is map_diff_trans_raw unfolding sym[OF eventually_cofinite]
  by (simp add: map_diff_fin_variability)

lift_definition map_add_trans :: "'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  is "\<lambda>\<tau>1 \<tau>2 n. map_add (\<tau>1 n) (\<tau>2 n)" unfolding sym[OF eventually_cofinite]
  by (simp add: map_add_fin_variability)

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

(* TODO : replace smt proof *)
lemma dom_map_diff_subseteq:
  "dom (map_diff m3 m1) \<subseteq> dom (map_diff m3 m2) \<union> dom (map_diff m2 m1)"
  by (smt UnCI domIff map_diff_def subsetI)

(* TODO : replace smt proof *)
lemma dom_map_diff_trans_post_raw:
  "dom (map_diff_trans_raw (trans_post_raw sig x \<tau> (t + dly)) \<tau> n) \<subseteq> {sig}"
  by (smt domIff fun_upd_apply insertCI map_diff_def subsetI trans_post_raw_def)

lemma dom_map_diff_trans_post:
  "dom (get_trans (map_diff_trans (trans_post sig x \<tau> (t + dly)) \<tau>) n)  \<subseteq> {sig}"
  by (transfer, simp add: dom_map_diff_trans_post_raw)

lemma dom_map_diff_purge_raw:
  "\<And>n. dom (map_diff_trans_raw (purge_raw dly \<tau> t sig cur_val) \<tau> n) \<subseteq> {sig}"
proof
  fix n x
  let ?\<tau>' = "purge_raw dly \<tau> t sig cur_val"
  have "\<And>n. n \<in> {0 .. t} \<union> {t + dly <..} \<Longrightarrow> ?\<tau>' n = \<tau> n"
    using purge_raw_before_now_unchanged purge_raw_after_delay_unchanged
    by (metis Un_iff atLeastAtMost_iff greaterThan_iff)
  hence "\<And>n. n \<in> {0 .. t} \<union> {t + dly <..} \<Longrightarrow> dom (map_diff (?\<tau>' n) (\<tau> n)) = {}"
    by auto
  moreover have "\<And>n. n \<in> {t <.. t + dly} \<Longrightarrow> dom (map_diff (?\<tau>' n) (\<tau> n)) \<subseteq> {sig}"
  proof
    fix n x
    assume "n \<in> {t <.. t + dly}"
    have "x = sig \<or> x \<noteq> sig" by auto
    moreover
    { assume "x \<noteq> sig"
      hence "?\<tau>' n x = \<tau> n x"
        using purge_raw_does_not_affect_other_sig by metis
      hence "x \<notin> dom (map_diff (purge_raw dly \<tau> t sig cur_val n) (\<tau> n))"
        by (simp add: domIff map_diff_def)
      hence "n \<in> {t<..t + dly} \<Longrightarrow> x \<in> dom (map_diff (purge_raw dly \<tau> t sig cur_val n) (\<tau> n))
                                                                                       \<Longrightarrow> x \<in> {sig}"
        by auto }
    moreover
    { assume "x = sig"
      hence "n \<in> {t<..t + dly} \<Longrightarrow> x \<in> dom (map_diff (purge_raw dly \<tau> t sig cur_val n) (\<tau> n))
                                                                                       \<Longrightarrow> x \<in> {sig}"
        by auto }
    ultimately show "n \<in> {t<..t + dly} \<Longrightarrow> x \<in> dom (map_diff (purge_raw dly \<tau> t sig cur_val n)(\<tau> n))
                                                                                       \<Longrightarrow> x \<in> {sig}"
      by auto
  qed
  ultimately show "x \<in> dom (map_diff (purge_raw dly \<tau> t sig cur_val n) (\<tau> n)) \<Longrightarrow> x \<in> {sig}"
    by (metis domIff insertCI map_diff_def purge_raw_does_not_affect_other_sig)
qed

lemma dom_map_diff_purge:
  "\<And>n. dom (get_trans (map_diff_trans (purge dly \<tau> t sig cur_val) \<tau>) n) \<subseteq> {sig}"
   by (transfer, simp add:dom_map_diff_purge_raw)

lemma dom_map_diff_purge2:
  fixes \<tau> dly t sig cur_val
  defines "\<tau>_raw n \<equiv> get_trans \<tau> n"
  defines "\<tau>'_raw n \<equiv> get_trans (purge dly \<tau> t sig cur_val) n"
  shows "\<And>n. dom (map_diff_trans_raw \<tau>'_raw \<tau>_raw n) \<subseteq> {sig}"
  unfolding assms by(transfer, metis dom_map_diff_purge_raw)

lemma dom_map_diff_inr_post:
  fixes sig x cur_val \<tau> t dly n
  defines "\<tau>' \<equiv> inr_post sig x cur_val \<tau> t dly"
  shows "dom (get_trans (map_diff_trans \<tau>' \<tau>) n) \<subseteq> {sig}"
proof (cases "is_stable dly \<tau> t sig cur_val")
  case True
  then show ?thesis using dom_map_diff_trans_post[of "sig" "x" "\<tau>" "t" "dly" "n"]
    unfolding assms inr_post_def by simp
next
  case False
  define \<tau>' where "\<tau>' \<equiv> (purge dly \<tau> t sig cur_val)"
  hence "get_trans (inr_post sig x cur_val \<tau> t dly) n = get_trans (trans_post sig x \<tau>' (t + dly)) n"
    unfolding inr_post_def \<tau>'_def using False by auto
  moreover have "dom (get_trans (map_diff_trans (trans_post sig x \<tau>' (t + dly)) \<tau>') n) \<subseteq> {sig}"
    using dom_map_diff_trans_post by metis
  moreover have "dom (get_trans (map_diff_trans \<tau>' \<tau>) n) \<subseteq> {sig}"
    using dom_map_diff_purge[of "dly" "\<tau>" "t" "sig" "cur_val" "n"] unfolding \<tau>'_def by auto
  ultimately show ?thesis unfolding assms using dom_map_diff_subseteq
    by (metis (no_types, lifting) Un_empty_right map_diff_trans.rep_eq subset_Un_eq subset_singletonD)
qed

lemma seq_stmts_modify_local_only_raw:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
  shows "\<And>n. dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n)) \<subseteq> set (signals_in ss)"
  using assms
proof (induction ss arbitrary: \<tau> \<tau>')
  case (Bcomp ss1 ss2)
  define \<tau>'' where "\<tau>'' \<equiv> b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
  hence *: "b_seq_exec t \<sigma> \<gamma> \<theta> (Bcomp ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>''"
    unfolding \<tau>''_def by auto
  have **: "\<And>n. dom (map_diff (get_trans \<tau>'' n) (get_trans \<tau> n)) \<subseteq> signals_of ss1"
    using Bcomp(1)[of "\<tau>" "\<tau>''"] unfolding \<tau>''_def by auto
  have ***: "\<And>n. dom (map_diff (get_trans \<tau>' n) (get_trans \<tau>'' n)) \<subseteq> signals_of ss2"
    using Bcomp(2)[of "\<tau>''" "\<tau>'"] * Bcomp(3) by auto

  have "dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n))
                                                \<subseteq> dom (map_diff (get_trans \<tau>'  n) (get_trans \<tau>'' n))
                                                \<union> dom (map_diff (get_trans \<tau>'' n) (get_trans \<tau>   n))"
    using dom_map_diff_subseteq by metis
  also have "... \<subseteq> signals_of ss2 \<union> dom (map_diff (get_trans \<tau>'' n) (get_trans \<tau> n))"
    using ***[of "n"]  by(auto intro: Un_mono)
  also have "... \<subseteq> signals_of ss2 \<union> signals_of ss1"
    using **[of "n"] by (auto intro:Un_mono)
  finally show ?case by auto
next
  case (Bguarded x1 ss1 ss2)
  have "beval t \<sigma> \<gamma> \<theta> x1 = True \<or> beval t \<sigma> \<gamma> \<theta> x1 = False" (is "?true \<or> ?false")
    by auto
  moreover
  { assume "?true"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded x1 ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss1 \<tau>"
      by auto
    hence "... = \<tau>'"
      using Bguarded(3) by auto
    hence "dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n)) \<subseteq> signals_of ss1"
      using Bguarded(1) by auto
    hence ?case
      by auto }
  moreover
  { assume "?false"
    hence "b_seq_exec t \<sigma> \<gamma> \<theta> (Bguarded x1 ss1 ss2) \<tau> = b_seq_exec t \<sigma> \<gamma> \<theta> ss2 \<tau>"
      by auto
    hence "... = \<tau>'" using Bguarded by auto
    hence "dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n)) \<subseteq> signals_of ss2" using Bguarded
      by auto
    hence ?case by auto }
  ultimately show ?case by auto
next
  case (Bassign_trans sig e dly)
  define x where "x = (beval t \<sigma> \<gamma> \<theta> e)"
  hence "\<tau>' = trans_post sig x \<tau> (t + dly)"
    using Bassign_trans by auto
  with dom_map_diff_trans_post show ?case
    by (metis list.set(1) list.simps(15) map_diff_trans.rep_eq signals_in.simps(2))
next
  case (Bassign_inert sig e dly)
  define x where "x = (beval t \<sigma> \<gamma> \<theta> e)"
  hence "\<tau>' = inr_post sig x (\<sigma> sig) \<tau> t dly"
    using Bassign_inert by auto
  then show ?case
    by (metis dom_map_diff_inr_post list.set(1) list.simps(15) map_diff_trans.rep_eq
              signals_in.simps(3))
next
  case Bnull
  then show ?case by auto
qed

text \<open>An important theorem: the semantics of sequential statements only modifies local variables.\<close>

theorem seq_stmts_modify_local_only:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>')"
  shows "\<And>n. dom (get_trans (map_diff_trans \<tau>' \<tau>) n) \<subseteq> set (signals_in ss)"
  using seq_stmts_modify_local_only_raw[OF assms] by (transfer)

fun contain_null :: "'signal seq_stmt \<Rightarrow> bool" where
  "contain_null Bnull = True"
| "contain_null (Bassign_inert s expr n) = False"
| "contain_null (Bassign_trans s expr n) = False"
| "contain_null (Bguarded guard ss1 ss2) \<longleftrightarrow> contain_null ss1 \<or> contain_null ss2"
| "contain_null (Bcomp ss1 ss2) \<longleftrightarrow> contain_null ss1 \<or> contain_null ss2"

subsubsection \<open>Semantics of @{typ "'signal conc_stmt"}\<close>

text \<open>The semantics for the concurrent statement is very simple: execute each process independently
and then merge its result. To merge the results of all of the processes, the following function
@{term "clean_zip"} is used. Search for @{term "b_conc_exec"} for the semantics of concurrent
statements. \<close>

definition clean_zip_raw :: "'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow> 'signal trans_raw \<Rightarrow>
                                                                                  'signal trans_raw"
  where
  "clean_zip_raw \<tau> \<tau>\<^sub>1 \<tau>\<^sub>2 = (let \<tau>\<^sub>1_stripped = \<lambda>n. map_diff (\<tau>\<^sub>1 n) (\<tau> n);
                               \<tau>\<^sub>2_stripped = \<lambda>n. map_diff (\<tau>\<^sub>2 n) (\<tau> n);
                               zipped = \<lambda>n. map_add (\<tau>\<^sub>1_stripped n) (\<tau>\<^sub>2_stripped n)
                           in
                            (\<lambda>n. map_add (\<tau> n) (zipped n))
                          )"

text \<open>These two properties are taken directly from @{cite "VanTassel1995"} directly. I prove them
as a sanity check that this formalisation is a faithful formalisation.\<close>

theorem van_tassel_first_prop:
  "clean_zip_raw (\<lambda>n. Map.empty) \<tau>1 \<tau>2 = (\<lambda>n. map_add (\<tau>1 n) (\<tau>2 n))"
  unfolding clean_zip_raw_def Let_def by auto

theorem van_tassel_second_prop:
  fixes t t1 t2
  defines "dom1 n \<equiv> dom (map_diff (t1 n) (t n))"
  defines "dom2 n \<equiv> dom (map_diff (t2 n) (t n))"
  assumes "\<And>n. disjnt (dom1 n) (dom2 n)"
  shows "clean_zip_raw t t1 t2 = clean_zip_raw t t2 t1"
proof
  fix x
  define t1_stripped where "t1_stripped \<equiv> \<lambda>n. map_diff (t1 n) (t n)"
  define t2_stripped where "t2_stripped \<equiv> \<lambda>n. map_diff (t2 n) (t n)"
  define zipped where "zipped \<equiv> \<lambda>n. map_add (t1_stripped n) (t2_stripped n)"
  define zipped' where "zipped' \<equiv> \<lambda>n. map_add (t2_stripped n) (t1_stripped n)"

  have *: "\<And>n. dom (t1_stripped n) \<inter> dom (t2_stripped n) = {}"
    using assms unfolding t1_stripped_def t2_stripped_def disjnt_def
    by auto
  have "zipped = zipped'"
    unfolding zipped_def zipped'_def using * map_add_comm by metis
  thus "clean_zip_raw t t1 t2 x = clean_zip_raw t t2 t1 x"
    unfolding clean_zip_raw_def Let_def zipped_def zipped'_def t1_stripped_def t2_stripped_def
    by metis
qed

lemma dom_map_diff_clean_zip_union:
  "\<And>n. dom (map_diff_trans_raw (clean_zip_raw \<tau> \<tau>' \<tau>'') \<tau> n) \<subseteq>
                                  dom (map_diff_trans_raw \<tau>' \<tau> n) \<union> dom (map_diff_trans_raw \<tau>'' \<tau> n)"
proof
  fix n x
  assume prem: "x \<in> dom (map_diff (clean_zip_raw \<tau> \<tau>' \<tau>'' n) (\<tau> n))"
  define  \<tau>\<^sub>1_stripped where "\<tau>\<^sub>1_stripped \<equiv> \<lambda>n. map_diff (\<tau>' n) (\<tau> n)"
  define  \<tau>\<^sub>2_stripped where "\<tau>\<^sub>2_stripped \<equiv> \<lambda>n. map_diff (\<tau>'' n) (\<tau> n)"
  define  zipped where "zipped \<equiv> \<lambda>n. map_add (\<tau>\<^sub>1_stripped n) (\<tau>\<^sub>2_stripped n)"

  have "\<tau> n x \<noteq> None \<or> \<tau> n x = None" by auto
  moreover
  { assume "\<tau> n x \<noteq> None"
    then obtain val1 and val2 where
      "(clean_zip_raw \<tau> \<tau>' \<tau>'' n) x = Some val1" and "\<tau> n x = Some val2" and "val1 \<noteq> val2"
      using mem_dom_map_diff_obtains[OF prem] by metis
    hence "zipped n x = Some val1"
      unfolding clean_zip_raw_def Let_def  \<tau>\<^sub>1_stripped_def \<tau>\<^sub>2_stripped_def zipped_def
      by (simp add:  map_add_Some_iff)
    hence "x \<in> dom (map_diff (\<tau>' n) (\<tau> n)) \<union> dom (map_diff (\<tau>'' n) (\<tau> n))"
      unfolding zipped_def \<tau>\<^sub>1_stripped_def \<tau>\<^sub>2_stripped_def by auto }
  moreover
  { assume "\<tau> n x = None"
    hence "x \<in> dom (clean_zip_raw \<tau> \<tau>' \<tau>'' n)"
      using prem  by (metis domIff map_diff_def)
    hence "x \<in> dom (map_diff (\<tau>' n) (\<tau> n)) \<union> dom (map_diff (\<tau>'' n) (\<tau> n))"
      using \<open>\<tau> n x = None\<close> unfolding zipped_def \<tau>\<^sub>1_stripped_def \<tau>\<^sub>2_stripped_def
      by (metis (no_types, lifting) clean_zip_raw_def domIff dom_map_add map_add_dom_app_simps(3)
          sup_commute) }
  ultimately show "x \<in> dom (map_diff (\<tau>' n) (\<tau> n)) \<union> dom (map_diff (\<tau>'' n) (\<tau> n))"
    by auto
qed

lift_definition clean_zip :: "'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow>
                                                                                'signal transaction"
  is clean_zip_raw unfolding clean_zip_raw_def sym[OF eventually_cofinite]
  by (simp add: map_add_fin_variability map_diff_fin_variability)

text \<open>Note that in the following semantics, if the process is not activated --- meaning the
sensitivity list does not contain recently changed signals --- then the returned transaction is an
empty transaction.\<close>

fun b_conc_exec :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  where
    "b_conc_exec t \<sigma> \<gamma> \<theta> (process sl : ss) \<tau> =
                                  (if disjnt sl \<gamma> then \<tau> else b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>)"
  | "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =
           (let \<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>;  \<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau> in clean_zip \<tau> \<tau>1 \<tau>2)"

abbreviation  b_conc_exec_abb :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool"
  ("_ , _ , _ , _ \<turnstile> <_ , _> \<longrightarrow>\<^sub>c _") where
  "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<equiv> (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>')"

theorem conc_stmts_modify_local_only_raw:
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  shows "\<And>n. dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n)) \<subseteq> set (signals_from cs)"
  using assms
proof (induction cs arbitrary:\<tau>')
  case (Bpar cs1 cs2)
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence *: "\<And>n. dom (map_diff (get_trans \<tau>1 n) (get_trans \<tau> n)) \<subseteq> set (signals_from cs1)"
    using Bpar(1) by auto
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence **: "\<And>n. dom (map_diff (get_trans \<tau>2 n) (get_trans \<tau> n)) \<subseteq> set (signals_from cs2)"
    using Bpar(2) by auto
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = clean_zip \<tau> \<tau>1 \<tau>2"
    unfolding \<tau>1_def \<tau>2_def by auto
  hence "... = \<tau>'"
    using Bpar(3) by auto
  hence "\<And>n. dom (map_diff (get_trans \<tau>' n) (get_trans \<tau> n))
                                                   \<subseteq> dom (map_diff (get_trans \<tau>1 n) (get_trans \<tau> n))
                                                   \<union> dom (map_diff (get_trans \<tau>2 n) (get_trans \<tau> n))"
    using dom_map_diff_clean_zip_union
    by (metis clean_zip.rep_eq)
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
  shows "\<And>n. dom (get_trans (map_diff_trans \<tau>' \<tau>) n) \<subseteq> set (signals_from cs)"
  using assms
  by (metis conc_stmts_modify_local_only_raw map_diff_trans.rep_eq)

lemma parallel_comp_commute':
  assumes "conc_stmt_wf (cs1 || cs2)"
  assumes "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  shows "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
proof -
  define \<tau>1 where "\<tau>1 = b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  hence m_diff1: "\<And>n. dom (get_trans (map_diff_trans \<tau>1 \<tau>) n) \<subseteq> set (signals_from cs1)"
    using conc_stmts_modify_local_only by metis
  define \<tau>2 where "\<tau>2 = b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  hence m_diff2: "\<And>n. dom (get_trans (map_diff_trans \<tau>2 \<tau>) n) \<subseteq> set (signals_from cs2)"
    using conc_stmts_modify_local_only by metis
  have "\<tau>' = clean_zip \<tau> \<tau>1 \<tau>2"
    using assms(2) unfolding \<tau>1_def \<tau>2_def by auto
  have "\<And>n. disjnt (dom (get_trans (map_diff_trans \<tau>1 \<tau>) n))
                    (dom (get_trans (map_diff_trans \<tau>2 \<tau>) n))"
    using m_diff1 m_diff2 assms(1)
    by (metis conc_stmt_wf_def disjnt_def disjnt_subset1 disjnt_subset2 distinct_append
              signals_from.simps(2))
  hence "clean_zip \<tau> \<tau>1 \<tau>2 = clean_zip \<tau> \<tau>2 \<tau>1"
    using van_tassel_second_prop[of "get_trans \<tau>1" "get_trans \<tau>" "get_trans \<tau>2"]
    by (transfer) auto
  thus ?thesis
    using assms(2) `\<tau>' = clean_zip \<tau> \<tau>1 \<tau>2` unfolding \<tau>1_def \<tau>2_def by auto
qed

text \<open>The first property we prove for the semantics of the concurrent statement is that two
processes are commutative.\<close>

theorem parallel_comp_commute:
  assumes "conc_stmt_wf (cs1 || cs2)"
  shows "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<longleftrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 || cs1, \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  using assms parallel_comp_commute' by metis

(* TODO: smt solver can find solution; failed to reconstruct. *)
lemma conjecture:
  "\<And>n. map_diff (clean_zip_raw t t1 t2 n) (t n) = (map_diff (t1 n) (t n)) ++ (map_diff (t2 n) (t n))"
  sorry

lemma clean_zip_raw_assoc:
  "clean_zip_raw t (clean_zip_raw t t1 t2) t3 = clean_zip_raw t t1 (clean_zip_raw t t2 t3)"
proof
  fix x

  define \<tau>\<^sub>1_stripped where "\<tau>\<^sub>1_stripped \<equiv> \<lambda>n. map_diff (t1 n) (t n)"
  define \<tau>\<^sub>2_stripped where "\<tau>\<^sub>2_stripped \<equiv> \<lambda>n. map_diff (t2 n) (t n)"
  define \<tau>\<^sub>3_stripped where "\<tau>\<^sub>3_stripped \<equiv> \<lambda>n. map_diff (t3 n) (t n)"
  define zipped12 where "zipped12 \<equiv> \<lambda>n. (\<tau>\<^sub>1_stripped n) ++ (\<tau>\<^sub>2_stripped n)"
  define zipped23 where "zipped23 \<equiv> \<lambda>n. (\<tau>\<^sub>2_stripped n) ++ (\<tau>\<^sub>3_stripped n)"
  define cz12_stripped where "cz12_stripped \<equiv> \<lambda>n. map_diff ((clean_zip_raw t t1 t2) n) (t n)"
  define cz23_stripped where "cz23_stripped \<equiv> \<lambda>n. map_diff ((clean_zip_raw t t2 t3) n) (t n)"

  have *: "cz12_stripped = (\<lambda>n. (\<tau>\<^sub>1_stripped n) ++ (\<tau>\<^sub>2_stripped n))"
    using conjecture unfolding \<tau>\<^sub>1_stripped_def \<tau>\<^sub>2_stripped_def cz12_stripped_def
    by metis
  have **: "cz23_stripped = (\<lambda>n. (\<tau>\<^sub>2_stripped n) ++ (\<tau>\<^sub>3_stripped n))"
    using conjecture unfolding \<tau>\<^sub>2_stripped_def \<tau>\<^sub>3_stripped_def cz23_stripped_def
    by metis
  have "clean_zip_raw t (clean_zip_raw t t1 t2) t3 x =
                                          (t x) ++ (cz12_stripped x) ++ (\<tau>\<^sub>3_stripped x)"
    unfolding clean_zip_raw_def Let_def cz12_stripped_def \<tau>\<^sub>3_stripped_def by auto
  also have "... = (t x) ++ (\<tau>\<^sub>1_stripped x) ++ (\<tau>\<^sub>2_stripped x) ++ (\<tau>\<^sub>3_stripped x)"
    using * by auto
  finally have "clean_zip_raw t (clean_zip_raw t t1 t2) t3 x =
                                      (t x) ++ (\<tau>\<^sub>1_stripped x) ++ (\<tau>\<^sub>2_stripped x) ++ (\<tau>\<^sub>3_stripped x)"
    by auto
  moreover have "clean_zip_raw t t1 (clean_zip_raw t t2 t3) x =
                                      (t x) ++ (\<tau>\<^sub>1_stripped x) ++ (\<tau>\<^sub>2_stripped x) ++ (\<tau>\<^sub>3_stripped x)"
    using ** unfolding clean_zip_raw_def Let_def cz23_stripped_def \<tau>\<^sub>1_stripped_def \<tau>\<^sub>2_stripped_def
    \<tau>\<^sub>3_stripped_def by (metis map_add_assoc)
  ultimately show " clean_zip_raw t (clean_zip_raw t t1 t2) t3 x =
                                                        clean_zip_raw t t1 (clean_zip_raw t t2 t3) x"
    by auto
qed

lemma clean_zip_assoc:
  "clean_zip \<tau> (clean_zip \<tau> \<tau>1 \<tau>2) \<tau>3 = clean_zip \<tau> \<tau>1 (clean_zip \<tau> \<tau>2 \<tau>3)"
  by transfer (simp add:clean_zip_raw_assoc)

text \<open>The second property of the semantics of concurrent statements: they are associative. Together
with the first property of being commutative, they in some sense provide a guarantee that they are
truly parallel; we can execute whichever process in any order and the merging will always be the
same.\<close>

theorem parallel_comp_assoc:
  "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <(cs1 ||  cs2) || cs3 , \<tau>> \<longrightarrow>\<^sub>c \<tau>') \<longleftrightarrow>
                                                   (t, \<sigma>, \<gamma>, \<theta> \<turnstile> < cs1 || (cs2  || cs3), \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
  by (auto simp add: clean_zip_assoc)

text \<open>The Language Reference Manual for VHDL stipulates that each process will be executed initially
regardless of their sensitivity list.\<close>

inductive init :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace
                    \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool"
  ("_ , _ , _ , _ \<turnstile> <_ , _> \<longrightarrow> start _") where
  "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss , \<tau>> \<longrightarrow>\<^sub>s \<tau>') \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <process sl : ss , \<tau>> \<longrightarrow> start \<tau>')"
| "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 , \<tau>> \<longrightarrow> start \<tau>') \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs2 , \<tau>> \<longrightarrow> start \<tau>'') \<Longrightarrow>
                                   (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs1 || cs2, \<tau>> \<longrightarrow> start (clean_zip \<tau> \<tau>' \<tau>''))"

fun init' :: "time \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                             'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction"
  where
    "init' t \<sigma> \<gamma> \<theta> (process sl : ss) \<tau> =  b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>"
  | "init' t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> =
                       (let \<tau>1 = init' t \<sigma> \<gamma> \<theta> cs1 \<tau>;  \<tau>2 = init' t \<sigma> \<gamma> \<theta> cs2 \<tau> in clean_zip \<tau> \<tau>1 \<tau>2)"

subsubsection \<open>Semantics of simulation\<close>

text \<open>The other aspect of the semantics is how to simulate, or in a sense execute, VHDL text. One
has to deal with the advance of simulation time. Rather than advancing time naturally, the simulation
proceeds to the "next interesting point of computation" @{cite "VanTassel1995"}. The following
function does exactly this purpose.\<close>

(* TODO : it should be the smallest time larger than t*)
definition next_time :: "time \<Rightarrow> 'signal transaction \<Rightarrow> time" where
  "next_time t \<tau>' = (if \<tau>' = 0 then t else LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"

lemma [simp]:
  "next_time t 0 = t"
  unfolding next_time_def by auto

lemma next_time_at_least:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
  shows "t \<le> next_time t \<tau>'"
proof (cases "\<tau>' = 0")
  case True
  then show ?thesis by auto
next
  case False
  hence *: "\<exists>n. dom (get_trans \<tau>' n) \<noteq> {}"
    by transfer' (metis (no_types, hide_lams) dom_eq_empty_conv map_add_subsumed1 map_add_subsumed2
       map_le_def zero_fun_def zero_option_def)
  have "t \<le> (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
  proof (rule ccontr)
    assume "\<not> t \<le> (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
    hence "(LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) < t" (is "?least < _")
      by auto
    with assms have "get_trans \<tau>' ?least = 0"
      by auto
    have "dom (get_trans \<tau>' ?least) \<noteq> {}"
      using LeastI_ex[OF *] by auto
    thus "False"
      by (metis \<open>get_trans \<tau>' (LEAST n. dom (get_trans \<tau>' n) \<noteq> {}) = 0\<close> dom_eq_empty_conv
                zero_fun_def zero_option_def)
  qed
  then show ?thesis
    unfolding next_time_def by auto
qed

lemma next_time_at_least2:
  assumes "next_time t \<tau>' = t'"
  shows "\<forall>n. n < t' \<longrightarrow> get_trans \<tau>' n = 0"
  using assms
proof (cases "\<tau>' = 0")
  case True
  then show ?thesis by auto
next
  case False
  hence "t' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
    using assms by (auto simp add: next_time_def)
  moreover have "\<And>n. dom (get_trans \<tau>' n) = {} \<longleftrightarrow> get_trans \<tau>' n = 0"
    by (simp add: zero_fun_def zero_option_def)
  ultimately have "t' = (LEAST n. get_trans \<tau>' n \<noteq> 0)"
    by auto
  then show ?thesis
    using not_less_Least by blast
qed

text \<open>At some point, a normal VHDL text would contain no more interesting computations. We check
this with the following @{term "quiet"} function. \<close>

definition quiet :: "'signal transaction \<Rightarrow> 'signal event \<Rightarrow> bool" where
  "quiet \<tau> evt = (if \<tau> = 0 \<and> evt = {} then True else False)"

text \<open>The function @{term "next_state"} is to update the state of computation in the next
interesting point of computation. \<close>

definition next_state :: "time \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal state" where
  "next_state t \<tau>' \<sigma> = (let m = get_trans \<tau>' (next_time t \<tau>') in override_on \<sigma> (the o m) (dom m))"

lemma [simp]:
  "override_on \<sigma> (the o (0 :: 'a \<rightharpoonup> bool)) (dom (0 :: 'a \<rightharpoonup> bool)) = \<sigma>"
  by (simp add: zero_fun_def zero_option_def)

text \<open>The function @{term "next_event"} checks whether the state at the next interesting point of
computation differs from the current state. Any signal which is different is listed as event.\<close>

definition next_event :: "time \<Rightarrow> 'signal transaction \<Rightarrow> 'signal state \<Rightarrow> 'signal event" where
  "next_event t \<tau>' \<sigma> = (let m = get_trans \<tau>' (next_time t \<tau>') in
                                                        {sig. sig \<in> dom m \<and> (the o m) sig \<noteq> \<sigma> sig})"

lemma [simp]:
  "{sig. sig \<in> dom (0 :: 'a \<rightharpoonup> bool) \<and> (the o (0 :: 'a \<rightharpoonup> bool)) sig \<noteq> \<sigma> sig} = {}"
  by (simp add:zero_option_def zero_fun_def)

text \<open>After we advance to the next interesting computation point, we need to save the behaviour so
that we can return this as the result in the end of the computation (either when it is quiet or
the maximum simulation time is reached).\<close>

definition add_to_beh :: "'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow> time \<Rightarrow> time
                                             \<Rightarrow> 'signal trace" where
  "add_to_beh \<sigma> \<gamma> \<theta> st fi = (if st < fi then Poly_Mapping.update st (Some o \<sigma>) \<theta> else \<theta>)"

lemma [simp]:
  "add_to_beh \<sigma> \<gamma> \<theta> t t = \<theta>"
  unfolding add_to_beh_def by (transfer, auto)

definition rem_curr_trans :: "time \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction" where
  "rem_curr_trans t \<tau> = Poly_Mapping.update t 0 \<tau>"

lemma [simp]:
  "rem_curr_trans t empty_trans = empty_trans"
  unfolding rem_curr_trans_def by (transfer, auto)

text \<open>The judgement or simulation rule. Three cases are considered here: 1) whether the maximum
simulation time has not reached yet and there are transactions to process; 2) whether there is no
more interesting computation (quiesced or quiet); and 3) whether the maximum simulation time is up.

The following semantic rule use a turnstile notation --- as in logic --- to determine what is the
context (or environment so to speak), what concurrent statement is being considered, what is the
predicted behaviour in the future (transaction), and lastly the result of the execution of VHDL text.
Check the mixfix notation used in the semantics below.

The left hand side of the turnstile contains simulation elements: time @{term "t :: time"},
state @{term "\<sigma> :: 'signal state"}, event @{term "\<gamma> :: 'signal event"}, and trace
@{term "\<theta> :: 'signal trace"}. This is the context to determine how a VHDL text shall progress.
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

inductive b_simulate_fin :: "time \<Rightarrow> time \<Rightarrow> 'signal  state \<Rightarrow> 'signal event \<Rightarrow> 'signal trace \<Rightarrow>
                            'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal trace \<Rightarrow> bool"
  ("_, _ , _ , _ , _ \<turnstile> <_ , _> \<leadsto> _") where

  \<comment> \<open>Business as usual: not quiesced yet and there is still time\<close>
  "    (t \<le> maxtime)
   \<Longrightarrow> (\<not> quiet \<tau> \<gamma>)
   \<Longrightarrow> (t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>')
   \<Longrightarrow> (maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh \<sigma> \<gamma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> res)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"

  \<comment> \<open>The simulation has quiesced and there is still time\<close>
| "    (t \<le> maxtime)
   \<Longrightarrow> (quiet \<tau> \<gamma>)
   \<Longrightarrow> Poly_Mapping.update t (Some o \<sigma>) \<theta> = res
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"

  \<comment> \<open>Time is up\<close>
| "  \<not> (t \<le> maxtime)
   \<Longrightarrow> (override_lookups_on_open_left \<theta> 0 maxtime t = res)
   \<Longrightarrow> (maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"

inductive_cases bau: "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"

lemma case_quiesce:
  assumes "t \<le> maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "res = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
  using bau[OF assms(3)] assms by auto

lemma case_timesup:
  assumes "\<not> (t \<le> maxtime)"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res)"
  shows "res = override_lookups_on_open_left \<theta> 0 maxtime t"
  using bau[OF assms(2)] assms by auto

lemma case_bau:
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  shows "(maxtime,
             next_time t \<tau>',
                next_state t \<tau>' \<sigma>,
                    next_event t \<tau>' \<sigma>,
                        add_to_beh \<sigma> \<gamma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> beh)"
  using bau[OF assms(4)] assms by auto

text \<open>An important theorem for any inductive definition; the computation should be deterministic.\<close>

theorem b_simulate_fin_deterministic:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res1"
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res2"
  shows "res2 = res1"
  using assms apply (induction arbitrary: res2 rule:b_simulate_fin.induct)
  using case_bau apply blast
  using case_quiesce apply blast
  using case_timesup by blast

inductive b_simulate :: "time \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trace \<Rightarrow> bool" where
  "     init' 0 def_state {} 0 cs empty_trans = \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def_state = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def_state = \<gamma>'
   \<Longrightarrow>  add_to_beh def_state {} 0 0 t' = beh'
   \<Longrightarrow>  maxtime, t', \<sigma>', \<gamma>', beh' \<turnstile> <cs, \<tau>'> \<leadsto> res
   \<Longrightarrow>  b_simulate maxtime cs res"

text \<open>Judgement @{term "b_simulate"} contains one rule only: executing the @{term "init'"} rule
before @{term "b_simulate_fin"}.\<close>


inductive_cases bau_init : "b_simulate maxtime cs res"

lemma case_bau':
  assumes "b_simulate maxtime cs res"
  assumes "init' 0 def_state {} 0 cs empty_trans = \<tau>'"
  shows "maxtime, next_time  0 \<tau>', next_state 0 \<tau>' def_state, next_event 0 \<tau>' def_state,
                             add_to_beh def_state {} 0 0 (next_time  0 \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> res"
  using bau_init[OF assms(1)] assms by auto

text \<open>Similar to the theorem accompanying @{term "b_simulate_fin"}, i.e.
@{thm "b_simulate_fin_deterministic"}, the rule @{term "b_simulate"} is also deterministic.\<close>

theorem b_sim_init_deterministic:
  assumes "b_simulate maxtime cs res1"
  assumes "b_simulate maxtime cs res2"
  shows "res2 = res1"
  using assms apply (induction arbitrary:res2 rule:b_simulate.induct)
  using case_bau' b_simulate_fin_deterministic by blast

subsubsection \<open>Small step semantics of simulation\<close>

text \<open>The motivation behind the formulation of small step semantic is due to code generation. We
want to simulate the behaviour of a VHDL text in Isabelle. Because the simulation function is
defined with inductive definition (we could not formalise it with function because it is possible
to have non terminating VHDL text), the property that the corresponding code is the same with
@{term "b_simulate_fin"} or @{term "b_simulate"} depends whether the VHDL text terminates or not.
We cannot talk about termination with big step semantics. Hence, we also formalise the small-step
semantics and prove (only one way) that the small step implies the big step semantics.\<close>

type_synonym 'signal configuration = "time \<times> 'signal  state \<times> 'signal event \<times> 'signal trace"

fun update_config :: "'signal configuration \<Rightarrow> 'signal transaction \<Rightarrow> 'signal configuration"
  where
  "update_config (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (let t' = next_time t \<tau>';
                                        \<sigma>' = next_state t \<tau>' \<sigma>;
                                        \<gamma>' = next_event t \<tau>' \<sigma>;
                                        \<theta>' = add_to_beh \<sigma> \<gamma> \<theta> t t'
                                    in (t', \<sigma>', \<gamma>', \<theta>'))"

inductive b_simulate_fin_ss :: "time \<Rightarrow> 'signal conc_stmt \<Rightarrow>
  'signal transaction \<times> 'signal configuration  \<Rightarrow>  'signal transaction \<times> 'signal configuration
                                                                                             \<Rightarrow> bool"
  where
   \<comment> \<open>Time is up\<close>
 "  \<not>  t \<le> maxtime
   \<Longrightarrow> override_lookups_on_open_left \<theta> 0 maxtime t = \<theta>'
   \<Longrightarrow> b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxtime + 1, \<sigma>, \<gamma>, \<theta>')"

   \<comment> \<open>The simulation has quiesced and there is still time\<close>
| "    t \<le> maxtime
   \<Longrightarrow> quiet \<tau> \<gamma>
   \<Longrightarrow> Poly_Mapping.update t (Some o \<sigma>) \<theta> = \<theta>'
   \<Longrightarrow> b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxtime + 1, \<sigma>, \<gamma>, \<theta>')"

   \<comment> \<open>Business as usual: not quiesced yet and there is still time\<close>
| "    t \<le> maxtime
   \<Longrightarrow> \<not> quiet \<tau> \<gamma>
   \<Longrightarrow> t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'
   \<Longrightarrow> update_config (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>')
   \<Longrightarrow> b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"

inductive_cases sim_ss_ic : "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"

lemma
  assumes "  \<not>  t \<le> maxtime"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxtime, \<sigma>, \<gamma>, res')"
  shows "override_lookups_on_open_left \<theta> 0 maxtime t = res'"
  using assms by (auto intro: sim_ss_ic)

lemma
  assumes "t \<le> maxtime"
  assumes "quiet \<tau> \<gamma>"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>, maxtime, \<sigma>, \<gamma>, res')"
  shows "Poly_Mapping.update t (Some o \<sigma>) \<theta> = res'"
  using assms by (auto intro:sim_ss_ic)

lemma
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  shows "update_config (t, \<sigma>, \<gamma>, \<theta>) \<tau>' = (t', \<sigma>', \<gamma>', \<theta>')"
  using assms by (auto intro:sim_ss_ic)

theorem b_simulate_fin_ss_deterministic:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1)"
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2)"
  shows "(\<tau>1, t1, \<sigma>1, \<gamma>1, \<theta>1) = (\<tau>2, t2, \<sigma>2, \<gamma>2, \<theta>2)"
  using assms
proof (induction arbitrary: \<tau>2 t2 \<sigma>2 \<gamma>2 \<theta>2 rule: b_simulate_fin_ss.induct)
  case (1 t maxtime \<theta> res' cs \<tau> \<sigma> \<gamma>)
  thus ?case
    by (auto intro!: sim_ss_ic[OF 1(3)])
next
  case (2 t maxtime \<tau> \<gamma> \<theta> \<sigma> res' cs)
  thus ?case
    by (auto intro!: sim_ss_ic[OF 2(4)])
next
  case (3 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' t' \<sigma>' \<gamma>' \<theta>')
  show ?case
  proof -
    have f1: "\<tau>2 = \<tau>'"
      using "3" sim_ss_ic by blast
    have "\<forall>A p pa pb pc pd n pe c na Aa nb.
         ((update_config (nb, pc, A::'a set, pa) (b_conc_exec nb pc A pa c (rem_curr_trans nb pb)) =
                                                                        (n, p, Aa, pe) \<or> quiet pb A)
      \<or> \<not> b_simulate_fin_ss na c (pb, nb, pc, A, pa) (pd, n, p, Aa, pe)) \<or> \<not> nb \<le> na"
      using sim_ss_ic by fastforce
    then show ?thesis
      using f1 by (metis (no_types) "3")
  qed
qed

lemma trans_post_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow>  \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (trans_post_raw sig x \<tau> (t + dly)) n = 0"
  using assms  by (auto simp add: trans_post_raw_def)

lemma trans_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (trans_post sig x \<tau> (t + dly)) n = 0"
  using assms by (transfer, auto simp add: trans_post_raw_preserve_trans_removal)

lemma purge_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (purge_raw dly \<tau> t sig (\<sigma> sig)) n = 0"
  using assms by (induction dly arbitrary:\<tau>) (auto simp add: Let_def)

lemma purge_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (purge dly \<tau> t sig (\<sigma> sig)) n = 0"
  using assms by (transfer, auto simp add: purge_raw_preserve_trans_removal)

lemma inr_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (inr_post sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal)

lemma b_seq_exec_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) n = 0"
  using assms
  by (induction ss arbitrary: \<tau>)
     (auto simp add: trans_post_preserve_trans_removal inr_post_preserve_trans_removal)

lemma clean_zip_raw_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>  n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>1 n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> \<tau>2 n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (clean_zip_raw \<tau> \<tau>1 \<tau>2) n = 0"
  using assms  by (simp add: clean_zip_raw_def)

lemma clean_zip_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau>  n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau>1 n = 0"
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau>2 n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (clean_zip \<tau> \<tau>1 \<tau>2) n = 0"
  using assms
  apply transfer'
  using clean_zip_raw_preserve_trans_removal by blast

lemma b_conc_exec_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow> get_trans (b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau>) n = 0"
  using assms
proof (induction cs arbitrary: \<tau>)
  case (Bpar cs1 cs2)
  let ?\<tau>1 = "b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau>"
  let ?\<tau>2 = "b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau>"
  have "b_conc_exec t \<sigma> \<gamma> \<theta> (cs1 || cs2) \<tau> = clean_zip \<tau> ?\<tau>1 ?\<tau>2"
    by auto
  have "\<And>n. n < t \<Longrightarrow> get_trans (clean_zip \<tau> ?\<tau>1 ?\<tau>2) n = 0"
    using clean_zip_preserve_trans_removal[OF Bpar(4)] Bpar by auto
  then show ?case  using Bpar(3) by auto
next
  case (Bsingle x1 x2)
  then show ?case by (auto simp add: b_seq_exec_preserve_trans_removal)
qed

lemma  rem_curr_trans_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (rem_curr_trans t \<tau>) n = 0"
  using assms by (simp add: lookup_update rem_curr_trans_def)

lemma b_conc_exec_rem_curr_trans_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows   "\<And>n. n < t \<Longrightarrow> get_trans (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) n = 0"
  using assms
  by (simp add: b_conc_exec_preserve_trans_removal rem_curr_trans_preserve_trans_removal)

abbreviation
  simulate_ss :: "time \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal transaction \<times> 'signal configuration
                                             \<Rightarrow>  'signal transaction \<times> 'signal configuration \<Rightarrow> bool"
  where "simulate_ss maxtime cs \<rho> \<rho>' \<equiv> star (b_simulate_fin_ss maxtime cs) \<rho> \<rho>'"

lemma lookup_zero_after_ss:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "\<And>n. t  \<le> n \<Longrightarrow> Poly_Mapping.lookup \<theta> n = 0"
  assumes "\<And>n. n  < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows   "\<And>n. t' \<le> n \<Longrightarrow> Poly_Mapping.lookup \<theta>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "t' \<le> n"
  assume *: "\<theta>' = override_lookups_on_open_left \<theta> 0 maxtime t"
  assume " t' = Suc maxtime " and "\<not> t \<le> maxtime" and "t' = Suc maxtime"
  hence "Suc maxtime \<le> t" and "t' \<le> t" by auto
  have "t < n \<or> n \<le> t" by auto
  moreover
  { assume "t < n"
    have "\<And>n. t < n \<Longrightarrow> get_trans \<theta>' n = get_trans \<theta> n"
      using * by transfer' auto
    with assms(2) have "get_trans \<theta>' n = 0"
      using `t < n` by auto }
  moreover
  { assume "n \<le> t"
    with `t' \<le> n` have "maxtime < n" unfolding `t' = Suc maxtime`
      by auto
    with * and `n \<le> t` have "get_trans \<theta>' n = 0"
      by transfer' auto }
  ultimately show "get_trans  \<theta>' n = 0" by auto
next
  fix n
  assume "t' \<le> n"
  assume "t \<le> maxtime"
  assume *: " \<theta>' =  Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>"
  assume t'_def: "t' = Suc maxtime"
  hence "get_trans \<theta>' n = get_trans \<theta> n"
    using * `t' \<le> n` `t \<le> maxtime` by transfer auto
  thus "get_trans \<theta>' n = 0"
    using `t' \<le> n` t'_def `t \<le> maxtime` assms(2) by auto
next
  fix n
  assume "t' \<le> n"
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))
          in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
                , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
                , add_to_beh \<sigma> \<gamma> \<theta> t t')) =
         (t', \<sigma>', \<gamma>', \<theta>')"
  hence t'_def: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))"
    and \<theta>'_def: "\<theta>' = (if t < t' then Poly_Mapping.update t (Some o \<sigma>) \<theta> else \<theta>)"
    unfolding Let_def add_to_beh_def by auto
  have "t < t' \<or> t' \<le> t" by auto
  moreover
  { assume "t < t'"
    hence **: "get_trans \<theta>' n = get_trans \<theta> n"
      using `t' \<le> n` `t < t'` \<theta>'_def unfolding add_to_beh_def
      by transfer' auto
    have *: "\<And>n. n < t \<Longrightarrow> get_trans (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) n = 0"
      using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(3)] by auto
    have "t \<le> t'"
      using next_time_at_least[OF *] t'_def by auto
    with `t' \<le> n` have "t \<le> n" by auto
    with assms(2) have " get_trans \<theta>' n = 0"
      using ** by auto }
  moreover
  { assume "t' \<le> t"
    define \<tau>'' where "\<tau>'' = b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)"
    have temp : "\<And>n. n  < t \<Longrightarrow> get_trans \<tau>'' n = 0"
      using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(3), of "t"]
      unfolding \<tau>''_def by auto
    have "t' = t" using next_time_at_least[OF temp, of "t"] t'_def `t' \<le> t` unfolding \<tau>''_def
      by auto
    hence "\<theta>' = \<theta>" using \<theta>'_def by auto
    hence "get_trans \<theta>' n = 0"
      using assms(2) `t' \<le> n` `t' = t` by auto }
  ultimately show "get_trans \<theta>' n = 0"
    by auto
qed

lemma small_step_preserve_trans_removal:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "\<And>n. n < t  \<Longrightarrow> get_trans \<tau> n = 0"
  shows   "\<And>n. n < t' \<Longrightarrow> get_trans \<tau>' n = 0"
proof (rule sim_ss_ic[OF assms(1)])
  fix n
  assume "t' = Suc maxtime"
  assume "\<not> t \<le> maxtime" hence "maxtime < t" by auto
  hence "t' \<le> t" using `t' = Suc maxtime` by auto
  assume "n < t'" and "\<tau>' = \<tau>"
  hence "n < t" using `t' \<le> t` by auto
  thus "get_trans \<tau>' n = 0"
    using assms(2) `\<tau>' = \<tau>` by auto
next
  fix n
  assume "t' = Suc maxtime" and "t \<le> maxtime"
  assume "quiet \<tau> \<gamma>"
  hence "\<tau> = 0"  by (meson quiet_def)
  moreover assume "\<tau>' = \<tau>"
  ultimately have "\<tau>' = 0" by auto
  thus "get_trans \<tau>' n = 0" by auto
next
  fix n
  assume \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)"
  hence *: "\<And>m. m < t \<Longrightarrow> get_trans \<tau>' m = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF assms(2)]
    by auto
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))
          in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
                , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
                , add_to_beh \<sigma> \<gamma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
  hence **: "t' = next_time t \<tau>'"
    unfolding Let_def \<tau>'_def by auto
  moreover assume "n < t'"
  moreover have "\<forall>n<t'. get_trans \<tau>' n = 0"
    using next_time_at_least2[OF sym[OF **]] by auto
  ultimately show "get_trans \<tau>' n = 0"
    by auto
qed

lemma ss_big_continue:
  assumes "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', t', \<sigma>', \<gamma>', \<theta>')"
  assumes "b_simulate_fin maxtime t' \<sigma>' \<gamma>' \<theta>' cs \<tau>' res"
  assumes "\<forall>n. t  \<le> n \<longrightarrow> Poly_Mapping.lookup \<theta> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> res"
proof (rule sim_ss_ic[OF assms(1)])
  assume "\<not> t \<le> maxtime" hence "maxtime < t" by auto
  hence "Suc (maxtime) \<le> t" by auto
  assume **: "\<theta>' = override_lookups_on_open_left \<theta> 0 maxtime t"
  hence *: "Poly_Mapping.lookup \<theta>' (Suc maxtime) = 0"
    using `Suc (maxtime) \<le> t` by (transfer') (auto)
  assume t'suc: "t' = Suc maxtime"
  have "res = override_lookups_on_open_left \<theta>' 0 maxtime t'"
    using case_timesup[OF _ assms(2)] t'suc by auto
  hence "res = Poly_Mapping.update (Suc maxtime) 0 \<theta>'"
    unfolding t'suc  by (transfer') (auto)
  with * have "res = \<theta>'"
    by (transfer') auto
  hence "override_lookups_on_open_left \<theta> 0 maxtime t = res"
    by (simp add: **)
  with `\<not> t \<le> maxtime` show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    by (auto intro:b_simulate_fin.intros)
next
  \<comment> \<open>from small step\<close>
  assume t'suc: "t' = Suc maxtime"
  assume "t \<le> maxtime"
  assume "(quiet \<tau> \<gamma>)"
  assume **: "\<theta>' = Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> "
  hence *: "Poly_Mapping.lookup \<theta>' (Suc maxtime) = 0"
    using assms(1) assms(3) t'suc
    by (metis \<open>t \<le> maxtime\<close> leD le_SucI lessI lookup_update)

  \<comment> \<open>from big step\<close>
  have "res = override_lookups_on_open_left \<theta>' 0 maxtime (Suc maxtime)"
    using t'suc case_timesup[OF _ assms(2)] t'suc by auto
  hence "res = Poly_Mapping.update (Suc maxtime) 0 \<theta>'"
    by (transfer') (auto)
  hence "res = \<theta>'"
    using * by (metis lookup_update poly_mapping_eqI)
  hence "Poly_Mapping.update t (Some o \<sigma>) \<theta> = res"
    by (simp add: "**")
  with `t \<le> maxtime` show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    using `quiet \<tau> \<gamma>` by (auto intro: b_simulate_fin.intros)
next
  assume asm1: "t \<le> maxtime"
  assume asm2: "\<not> quiet \<tau> \<gamma>"
  assume "(let t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))
     in (t', next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
           , next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>
           , add_to_beh \<sigma> \<gamma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
  hence t'_def: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))" and
        \<sigma>'_def: "\<sigma>' = next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>" and
        \<gamma>'_def: "\<gamma>' = next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>" and
        \<theta>'_def: "\<theta>' = add_to_beh \<sigma> \<gamma> \<theta> t t'"
    unfolding Let_def by auto
  assume \<tau>'_def: "\<tau>' = b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)"
  hence "(t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>')"
    by auto
  from b_simulate_fin.intros(1)[OF asm1 asm2 this] assms(2)
  show "maxtime, t , \<sigma> , \<gamma> , \<theta> \<turnstile> <cs , \<tau>> \<leadsto> res"
    unfolding t'_def \<sigma>'_def \<gamma>'_def \<theta>'_def \<tau>'_def by auto
qed

theorem small_step_implies_big_step:
  assumes "simulate_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')"
  assumes "\<forall>n. t  \<le> n \<longrightarrow> Poly_Mapping.lookup \<theta> n = 0"
  assumes "\<forall>n. n < t \<longrightarrow> get_trans \<tau> n = 0"
  shows "b_simulate_fin maxtime t \<sigma> \<gamma> \<theta> cs \<tau> (Poly_Mapping.update (maxtime + 1) 0 \<theta>')"
  using assms
proof (induction "(\<tau>, t, \<sigma>, \<gamma>, \<theta>)" "(\<tau>', maxtime + 1, \<sigma>', \<gamma>', \<theta>')" arbitrary: \<tau> t \<sigma> \<gamma> \<theta>
                                                                                  rule: star.induct)
  case refl
  have " Poly_Mapping.update (maxtime + 1) 0 \<theta>' =
                                      override_lookups_on_open_left \<theta>' 0 maxtime (maxtime + 1)"
    apply transfer' unfolding override_on_def by auto
  then show ?case
    using b_simulate_fin.intros(3)[of "maxtime + 1" "maxtime" "\<theta>'"
    "Poly_Mapping.update (maxtime + 1) 0 \<theta>'" "\<sigma>'" "\<gamma>'" "cs" "\<tau>'"] refl by auto
next
  case (step y)
  obtain \<tau>'' t'' \<sigma>'' \<gamma>'' \<theta>'' where y_def: "y = (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'')"
    using prod_cases5 by blast
  hence *: "b_simulate_fin_ss maxtime cs (\<tau>, t, \<sigma>, \<gamma>, \<theta>) (\<tau>'', t'', \<sigma>'', \<gamma>'', \<theta>'')"
    using step(1) by auto
  have **: "\<forall>n\<ge>t''. get_trans \<theta>'' n = 0"
    using "*" lookup_zero_after_ss step.prems by blast
  have ***: "\<forall>n<t''. get_trans \<tau>'' n = 0"
    using "*" small_step_preserve_trans_removal step.prems(2) by blast
  then show ?case
    using ss_big_continue[OF * step(3)[OF y_def **] step(4)]  by auto
qed

end