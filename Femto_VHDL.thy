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

lift_definition poly_mapping_of_fun ::  "(nat \<Rightarrow> 'a::zero) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, 'a) poly_mapping"
  is "\<lambda>f lo hi n. if n \<in> {lo ..< hi} then f n else 0"
  by auto

lemma poly_mapping_of_fun_empty_set:
  "poly_mapping_of_fun f 0 0 = 0"
  apply transfer' by auto

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

lemma zero_map:
  "(0 :: 'a \<rightharpoonup> 'b) x = None"
  by (auto simp add:zero_option_def zero_fun_def)

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

lemma finite_keys_to_transaction2:
  "finite (keys (to_transaction2 \<tau> s))"
  by auto

lemma lookups_equal_transaction2:
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  shows "\<And>n. n \<le> maxtime \<Longrightarrow> lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
  using assms apply transfer' unfolding to_trans_raw2_def by auto

lemma lookups_equal_transaction2_strict:
  assumes "\<And>n. n < maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  shows "\<And>n. n < maxtime \<Longrightarrow> lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
  using assms apply transfer' unfolding to_trans_raw2_def by auto

lemma to_transaction2_update:
  "to_transaction2 (Poly_Mapping.update n (Some \<circ> \<sigma>) \<theta>) sig =
                                       Poly_Mapping.update n (Some (\<sigma> sig)) (to_transaction2 \<theta> sig)"
  by (transfer', auto simp add: to_trans_raw2_def)

lemma keys_at_most_to_transaction2:
  assumes "\<forall>k \<in> keys \<theta>. k < t"
  shows "\<forall>k \<in> keys (to_transaction2 \<theta> s). k < t"
  using assms apply transfer' unfolding to_trans_raw2_def
  by (metis (mono_tags) mem_Collect_eq zero_fun_def)


subsection \<open>From transaction to function of time (signal)\<close>

lemma list_split3:
  assumes "sorted xs" and "distinct xs" and "xs \<noteq> []"
  assumes "hd xs \<le> x" and "x < last xs"
  shows "\<exists>ys y zs. xs = ys @ y # zs \<and> (\<forall>k \<in> set ys. k \<le> x) \<and> x < y"
proof -
  obtain ys where "takeWhile (\<lambda>n. n \<le> x) xs = ys"
    by auto
  moreover obtain y zs where "dropWhile (\<lambda>n. n \<le> x) xs = y # zs"
    by (metis append_Nil2 assms(3) assms(5) last_in_set le_less not_less_iff_gr_or_eq set_takeWhileD
        sorted.cases takeWhile_dropWhile_id)
  ultimately have "xs = ys @ y # zs \<and> x < y"
    using dropWhile_eq_Cons_conv by fastforce
  moreover have "(\<forall>k\<in>set ys. k \<le> x)"
    using `takeWhile (\<lambda>n. n \<le> x) xs = ys`  by (meson set_takeWhileD)
  ultimately show ?thesis
    by auto
qed

lemma takeWhile_last:
  fixes maxtime :: nat
  assumes "sorted ys" and "ys \<noteq> []" and "last ys \<le> maxtime"
  shows "takeWhile (\<lambda>k. k \<le> maxtime) ys = ys"
  unfolding takeWhile_eq_all_conv
proof
  fix k
  assume "k \<in> set ys"
  hence "k \<le> last ys"
    using `sorted ys` `ys \<noteq> []`
    by (metis insertE last_appendR last_in_set less_or_eq_imp_le list.distinct(1) list.set(2)
        sorted.simps(2) sorted_append split_list)
  thus "k \<le> maxtime"
    using assms by auto
qed

lemma takeWhile_lookup_same:
  fixes maxtime :: nat
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  shows "(takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>1))) =
         (takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>2)))"
proof (cases "\<tau>1 = 0")
  case True
  hence 0: "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>1)) = []"
    by auto
  have 1: "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>2 n = 0"
    using assms True by auto
  have "\<tau>2 = 0 \<or> \<tau>2 \<noteq> 0" by auto
  moreover
  { assume "\<tau>2 = 0"
    hence "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>2)) = []"
      by auto
    hence ?thesis  using 0 by auto }
  moreover
  { assume "\<tau>2 \<noteq> 0"
    then obtain ys where "ys = sorted_list_of_set (keys \<tau>2)" and "ys \<noteq> []"
      using degree_greater_zero_in_keys by force
    then obtain y ys' where "ys = y # ys'" by (meson neq_Nil_conv)
    hence "y \<in> set ys"
      by auto
    also have "... = keys \<tau>2"
      using `ys = sorted_list_of_set (keys \<tau>2)` by auto
    finally have "y \<in> keys \<tau>2" by auto
    hence "lookup \<tau>2 y \<noteq> 0"
      by auto
    have "maxtime < y"
    proof (rule ccontr)
      assume "\<not> maxtime < y" hence "y \<le> maxtime" by auto
      with 1 have "lookup \<tau>2 y = 0" by auto
      with `lookup \<tau>2 y \<noteq> 0` show "False" by auto
    qed
    hence "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>2)) = []"
      using `ys = sorted_list_of_set (keys \<tau>2)` `ys = y # ys'` `maxtime < y`
      by force
    hence ?thesis using 0 by auto }
  ultimately show ?thesis by blast
next
  case False
  then obtain xs where xs_def: "xs = sorted_list_of_set (keys \<tau>1)" and "xs \<noteq> []" and "sorted xs" and "distinct xs"
    using degree_greater_zero_in_keys by force
  then obtain x xs' where "xs = x # xs'" by (meson neq_Nil_conv)
  have "maxtime < x \<or> x \<le> maxtime" by auto
  moreover
  { assume "maxtime < x"
    hence 0: "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>1)) = []"
      using `xs = sorted_list_of_set (keys \<tau>1)` `xs = x # xs'` by force
    have "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = 0"
    proof (rule ccontr)
      fix n
      assume "n \<le> maxtime"
      assume "lookup \<tau>1 n \<noteq> 0"
      hence "n \<in> keys \<tau>1" by transfer' auto
      hence "ListMem n xs"
        using `xs = sorted_list_of_set (keys \<tau>1)` by (simp add: ListMem_iff)
      hence "hd xs \<le> n"
        using `xs \<noteq> []` `sorted xs`  by (metis ListMem.simps ListMem_iff less_or_eq_imp_le
        list.sel(1) list.sel(3) sorted.elims(2))
      hence "x \<le> n"
        using `xs = x # xs'` by auto
      with `maxtime < x` have "maxtime < n" by auto
      with `n \<le> maxtime` show "False" by auto
    qed
    hence 1: "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>2 n = 0"
      using assms by auto
    have "\<tau>2 = 0 \<or> \<tau>2 \<noteq> 0" by auto
    moreover
    { assume "\<tau>2 = 0"
      hence "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>2)) = []"
        by auto
      hence ?thesis  using 0 by auto }
    moreover
    { assume "\<tau>2 \<noteq> 0"
      then obtain ys where "ys = sorted_list_of_set (keys \<tau>2)" and "ys \<noteq> []"
        using degree_greater_zero_in_keys by force
      then obtain y ys' where "ys = y # ys'" by (meson neq_Nil_conv)
      hence "y \<in> set ys"
        by auto
      also have "... = keys \<tau>2"
        using `ys = sorted_list_of_set (keys \<tau>2)` by auto
      finally have "y \<in> keys \<tau>2" by auto
      hence "lookup \<tau>2 y \<noteq> 0"
        by auto
      have "maxtime < y"
      proof (rule ccontr)
        assume "\<not> maxtime < y" hence "y \<le> maxtime" by auto
        with 1 have "lookup \<tau>2 y = 0" by auto
        with `lookup \<tau>2 y \<noteq> 0` show "False" by auto
      qed
      hence "takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys \<tau>2)) = []"
        using `ys = sorted_list_of_set (keys \<tau>2)` `ys = y # ys'` `maxtime < y`
        by force
      hence ?thesis using 0 by auto }
    ultimately have ?thesis by blast }
  moreover
  { assume "x \<le> maxtime"
    hence "lookup \<tau>1 x = lookup \<tau>2 x"
      using assms by auto
    moreover have "lookup \<tau>1 x \<noteq> 0"
      using `xs = x # xs'` `xs = sorted_list_of_set (keys \<tau>1)`  by (metis \<open>xs \<noteq> []\<close> insert_iff
      list.set(2) lookup_not_eq_zero_eq_in_keys sorted_list_of_set(1) sorted_list_of_set.infinite)
    ultimately have "lookup \<tau>2 x \<noteq> 0"
      by auto
    hence "\<tau>2 \<noteq> 0"
      by auto
    then obtain ys where ys_def: "ys = sorted_list_of_set (keys \<tau>2)" and "ys \<noteq> []" and "sorted ys" and "distinct ys"
      using degree_greater_zero_in_keys by force
    then obtain y ys' where "ys = y # ys'" by (meson neq_Nil_conv)
    have "y \<le> maxtime"
    proof -
      have "x \<in> keys \<tau>2"
        using `lookup \<tau>2 x \<noteq> 0` by auto
      hence "x \<in> set ys"
        using `ys = sorted_list_of_set (keys \<tau>2)` by auto
      hence "y \<le> x"
        using `ys = y # ys'` `sorted ys` by auto
      thus "y \<le> maxtime"
        using `x \<le> maxtime` by auto
    qed

    have "maxtime < last xs \<or> last xs \<le> maxtime"
      by auto
    moreover
    { assume "maxtime < last xs"
      have "hd xs \<le> maxtime"
        using `xs = x # xs'` `x \<le> maxtime` by auto
      obtain xs1 cutx xs2 where "xs = xs1 @ cutx # xs2" and 3: "\<forall>k \<in> set xs1. k \<le> maxtime" and "maxtime < cutx"
        using list_split3[OF `sorted xs` `distinct xs` `xs \<noteq> []` `hd xs \<le> maxtime` `maxtime < last xs`]
        by auto
      have "\<forall>k \<in> set xs2. maxtime < k"
        using `sorted xs` `xs = xs1 @ cutx # xs2` `maxtime < cutx`
        by (meson less_le_trans sorted.simps(2) sorted_append)
      hence xs1_def: "takeWhile (\<lambda>n. n \<le> maxtime) xs = xs1"
        using "3" \<open>maxtime < cutx\<close> \<open>xs = xs1 @ cutx # xs2\<close> by auto
      have "maxtime < last ys \<or> last ys \<le> maxtime"
        by auto
      moreover
      { assume "maxtime < last ys"
        obtain ys1 cuty ys2 where "ys = ys1 @ cuty # ys2" and 4: "\<forall>k \<in> set ys1. k \<le> maxtime" and "maxtime < cuty"
          using list_split3[OF `sorted ys` `distinct ys` `ys \<noteq> []` _ `maxtime < last ys`]
          `ys = y # ys'` `y \<le> maxtime` by auto
        hence ys1_def: "takeWhile (\<lambda>n. n \<le> maxtime) ys = ys1"
          by auto
        have "\<forall>k \<in> set ys2. maxtime < k"
          using `sorted ys` `ys = ys1 @ cuty # ys2` `maxtime < cuty`
        by (meson less_le_trans sorted.simps(2) sorted_append)
        have "set xs1 = set ys1"
        proof (rule, rule_tac[!] subsetI)
          fix x
          assume "x \<in> set xs1"
          also have "... \<subseteq> set xs"
            using `xs = xs1 @ cutx # xs2` by auto
          finally have "x \<in> set xs"
            by auto
          hence "lookup \<tau>1 x \<noteq> 0"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          have "x \<le> maxtime"
            using `x \<in> set xs1` using 3 by auto
          hence "lookup \<tau>1 x = lookup \<tau>2 x"
            using assms by auto
          hence "lookup \<tau>2 x \<noteq> 0"
            using `lookup \<tau>1 x \<noteq> 0` by auto
          hence "x \<in> set ys"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          moreover have "x \<notin> set ys2" and "x \<noteq> cuty"
            using `\<forall>k \<in> set ys2. maxtime < k` `x \<le> maxtime` `maxtime < cuty` by auto
          ultimately show "x \<in> set ys1"
            using `ys = ys1 @ cuty # ys2` by auto
        next
          fix y
          assume "y \<in> set ys1"
          also have "... \<subseteq> set ys"
            using `ys = ys1 @ cuty # ys2` by auto
          finally have "y \<in> set ys"
            by auto
          hence "lookup \<tau>2 y \<noteq> 0"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          have "y \<le> maxtime"
            using `y \<in> set ys1` using 4 by auto
          hence "lookup \<tau>2 y = lookup \<tau>1 y"
            using assms by auto
          hence "lookup \<tau>1 y \<noteq> 0"
            using `lookup \<tau>2 y \<noteq> 0` by auto
          hence "y \<in> set xs"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          moreover have "y \<notin> set xs2" and "y \<noteq> cutx"
            using `\<forall>k \<in> set xs2. maxtime < k` `y \<le> maxtime` `maxtime < cutx` by auto
          ultimately show "y \<in> set xs1"
            using `xs = xs1 @ cutx # xs2` by auto
        qed

        moreover have "sorted xs1" and "sorted ys1" and "distinct xs1" and "distinct ys1"
          using `sorted xs` `sorted ys` `distinct xs` `distinct ys` `xs = xs1 @ cutx # xs2`
          `ys = ys1 @ cuty # ys2`
          using sorted_append apply blast
          using \<open>sorted ys\<close> \<open>ys = ys1 @ cuty # ys2\<close> sorted_append apply blast
          using \<open>distinct xs\<close> \<open>xs = xs1 @ cutx # xs2\<close> distinct_append apply blast
          using \<open>distinct ys\<close> \<open>ys = ys1 @ cuty # ys2\<close> distinct_append by blast

        ultimately have "xs1 = ys1"
          using sorted_distinct_set_unique by auto
        hence ?thesis
          using ys1_def xs1_def xs_def ys_def by auto }
      moreover
      { assume "last ys \<le> maxtime"
        hence "takeWhile (\<lambda>n. n \<le> maxtime) ys = ys"
          using `sorted ys` `ys \<noteq> []` takeWhile_last by auto
        have "set xs1 = set ys"
        proof (rule, rule_tac[!] subsetI)
          fix x
          assume "x \<in> set xs1"
          also have "... \<subseteq> set xs"
            using `xs = xs1 @ cutx # xs2` by auto
          finally have "x \<in> set xs"
            by auto
          hence "lookup \<tau>1 x \<noteq> 0"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          have "x \<le> maxtime"
            using `x \<in> set xs1` using 3 by auto
          hence "lookup \<tau>1 x = lookup \<tau>2 x"
            using assms by auto
          hence "lookup \<tau>2 x \<noteq> 0"
            using `lookup \<tau>1 x \<noteq> 0` by auto
          thus "x \<in> set ys"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
        next
          fix y
          assume "y \<in> set ys"
          hence "lookup \<tau>2 y \<noteq> 0"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          have "y \<le> last ys"
            using `ys \<noteq> []` `sorted ys` `y \<in> set ys`  using takeWhile_last by fastforce
          hence "y \<le> maxtime"
            using `last ys \<le> maxtime` by auto
          hence "lookup \<tau>2 y = lookup \<tau>1 y"
            using assms by auto
          hence "lookup \<tau>1 y \<noteq> 0"
            using `lookup \<tau>2 y \<noteq> 0` by auto
          hence "y \<in> set xs"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          moreover have "y \<notin> set xs2" and "y \<noteq> cutx"
            using `\<forall>k \<in> set xs2. maxtime < k` `y \<le> maxtime` `maxtime < cutx` by auto
          ultimately show "y \<in> set xs1"
            using `xs = xs1 @ cutx # xs2` by auto
        qed
        moreover have "sorted xs1 \<and> distinct xs1"
          using `sorted xs` `distinct xs` `xs = xs1 @ cutx # xs2`
          by (simp add: sorted_append)
        ultimately have "xs1 = ys"
          using sorted_distinct_set_unique `sorted ys` `distinct ys` by auto
        hence ?thesis
          using xs1_def xs_def ys_def `takeWhile (\<lambda>n. n \<le> maxtime) ys = ys` by metis }
      ultimately have ?thesis by auto }
    moreover
    { assume "last xs \<le> maxtime"
      hence "takeWhile (\<lambda>n. n \<le> maxtime) xs = xs"
        using takeWhile_last `sorted xs` `xs \<noteq> []` by auto
      have "maxtime < last ys \<or> last ys \<le> maxtime"
        by auto
      moreover
      { assume "maxtime < last ys"
        obtain ys1 cuty ys2 where "ys = ys1 @ cuty # ys2" and 4: "\<forall>k \<in> set ys1. k \<le> maxtime" and "maxtime < cuty"
          using list_split3[OF `sorted ys` `distinct ys` `ys \<noteq> []` _ `maxtime < last ys`]
          `ys = y # ys'` `y \<le> maxtime` by auto
        hence ys1_def: "takeWhile (\<lambda>n. n \<le> maxtime) ys = ys1"
          by auto
        have "\<forall>k \<in> set ys2. maxtime < k"
          using `sorted ys` `ys = ys1 @ cuty # ys2` `maxtime < cuty`
          by (meson le_less_trans not_less sorted.simps(2) sorted_append)
        have "set xs = set ys1"
        proof (rule, rule_tac[!] subsetI)
          fix x
          assume "x \<in> set xs"
          hence "lookup \<tau>1 x \<noteq> 0"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          have "x \<le> last xs"
            using `xs \<noteq> []` `sorted xs` \<open>x \<in> set xs\<close> takeWhile_last by fastforce
          hence "x \<le> maxtime"
            using `last xs \<le> maxtime` by auto
          hence "lookup \<tau>1 x = lookup \<tau>2 x"
            using assms by auto
          hence "lookup \<tau>2 x \<noteq> 0"
            using `lookup \<tau>1 x \<noteq> 0` by auto
          hence "x \<in> set ys"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          moreover have "x \<notin> set ys2" and "x \<noteq> cuty"
            using `\<forall>k \<in> set ys2. maxtime < k` `x \<le> maxtime` `maxtime < cuty` by auto
          ultimately show "x \<in> set ys1"
            using `ys = ys1 @ cuty # ys2` by auto
        next
          fix y
          assume "y \<in> set ys1"
          also have "... \<subseteq> set ys"
            using `ys = ys1 @ cuty # ys2` by auto
          finally have "y \<in> set ys"
            by auto
          hence "lookup \<tau>2 y \<noteq> 0"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          have "y \<le> maxtime"
            using `y \<in> set ys1` using 4 by auto
          hence "lookup \<tau>2 y = lookup \<tau>1 y"
            using assms by auto
          hence "lookup \<tau>1 y \<noteq> 0"
            using `lookup \<tau>2 y \<noteq> 0` by auto
          thus "y \<in> set xs"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
        qed

        moreover have "distinct ys1 \<and> sorted ys1"
          using `distinct ys` `sorted ys` `ys = ys1 @ cuty # ys2`  distinct_append sorted_append
          by blast
        ultimately have "xs = ys1"
          using sorted_distinct_set_unique `distinct xs` `sorted xs` by auto
        hence ?thesis
          using ys1_def xs_def ys_def `takeWhile (\<lambda>n. n \<le> maxtime) xs = xs` by auto }
      moreover
      { assume "last ys \<le> maxtime"
        hence "takeWhile (\<lambda>n. n \<le> maxtime) ys = ys"
          using `sorted ys` `ys \<noteq> []` takeWhile_last by metis
        have "set xs = set ys"
        proof (rule, rule_tac[!] subsetI)
          fix x
          assume "x \<in> set xs"
          hence "lookup \<tau>1 x \<noteq> 0"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
          have "x \<le> last xs"
            using `xs \<noteq> []` `sorted xs` \<open>x \<in> set xs\<close> takeWhile_last by fastforce
          hence "x \<le> maxtime"
            using `last xs \<le> maxtime` by auto
          hence "lookup \<tau>1 x = lookup \<tau>2 x"
            using assms by auto
          hence "lookup \<tau>2 x \<noteq> 0"
            using `lookup \<tau>1 x \<noteq> 0` by auto
          thus "x \<in> set ys"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
        next
          fix y
          assume "y \<in> set ys"
          hence "lookup \<tau>2 y \<noteq> 0"
            using `ys = sorted_list_of_set (keys \<tau>2)` by auto
          have "y \<le> last ys"
            using `ys \<noteq> []` `sorted ys` `y \<in> set ys`  using takeWhile_last by fastforce
          hence "y \<le> maxtime"
            using `last ys \<le> maxtime` by auto
          hence "lookup \<tau>2 y = lookup \<tau>1 y"
            using assms by auto
          hence "lookup \<tau>1 y \<noteq> 0"
            using `lookup \<tau>2 y \<noteq> 0` by auto
          thus "y \<in> set xs"
            using `xs = sorted_list_of_set (keys \<tau>1)` by auto
        qed
        hence "xs = ys"
          using sorted_distinct_set_unique `sorted xs` `distinct xs``sorted ys` `distinct ys` by auto
        hence ?thesis
          using xs_def ys_def `takeWhile (\<lambda>n. n \<le> maxtime) ys = ys` by metis }
      ultimately have ?thesis by auto }
    ultimately have ?thesis by auto }
  ultimately show ?thesis by auto
qed

lemma takeWhile_lookup_same_strict:
  fixes maxtime :: nat
  assumes "\<And>n. n < maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  shows "(takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys \<tau>1))) =
         (takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys \<tau>2)))"
proof (cases "maxtime \<noteq> 0")
  case True
  hence "\<And>n. n \<le> maxtime - 1 \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
    using assms by auto
  hence "(takeWhile (\<lambda>n. n \<le> maxtime - 1) (sorted_list_of_set (keys \<tau>1))) =
         (takeWhile (\<lambda>n. n \<le> maxtime - 1) (sorted_list_of_set (keys \<tau>2)))"
    using takeWhile_lookup_same by auto
  moreover have "takeWhile (\<lambda>n. n \<le> maxtime - 1) (sorted_list_of_set (keys \<tau>1)) =
                 takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys \<tau>1))"
    by (metis Suc_pred' True less_Suc_eq_le neq0_conv)
  moreover have "takeWhile (\<lambda>n. n \<le> maxtime - 1) (sorted_list_of_set (keys \<tau>2)) =
                 takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys \<tau>2))"
    by (metis Suc_pred' True less_Suc_eq_le neq0_conv)
  ultimately show ?thesis by auto
next
  case False hence "maxtime = 0" by auto
  then show ?thesis
    by (metis (full_types) last_in_set not_less_zero set_takeWhileD)
qed

fun inf_key :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
  "inf_key ks n = (case takeWhile (\<lambda>k. k \<le> n) ks of [] \<Rightarrow> None | ks' \<Rightarrow> Some (last ks'))"

lemma inf_key_alt_def:
  assumes "sorted (a # ks)"
  shows "inf_key (a # ks) n = (if a \<le> n \<and> inf_key ks n = None then Some a else inf_key ks n)"
proof -
  have "a \<le> n \<or> n < a" by auto
  moreover
  { assume "a \<le> n"
    hence "takeWhile (\<lambda>k. k \<le> n) (a # ks) = a # takeWhile (\<lambda>k. k \<le> n) ks"
      by auto
    hence "inf_key (a # ks) n = (case a # takeWhile (\<lambda>k. k \<le> n) ks of [] \<Rightarrow> None | ks' \<Rightarrow> Some (last ks'))"
      by auto
    also have "... = (if takeWhile (\<lambda>k. k \<le> n) ks = [] then Some a else Some (last (takeWhile (\<lambda>k. k \<le> n) ks)))"
      by auto
    also have "... = (if inf_key ks n = None then Some a else inf_key ks n)"
      by (auto split:list.splits)
    finally have "inf_key (a # ks) n = (if inf_key ks n = None then Some a else inf_key ks n)"
      by auto
    hence ?thesis using `a \<le> n` by auto }
  moreover
  { assume "n < a"
    hence "takeWhile (\<lambda>k. k \<le> n) (a # ks) = []"
      by auto
    hence "inf_key (a # ks) n = None"
      by auto
    moreover have "inf_key ks n = None"
      using `sorted (a # ks)`
      by (metis \<open>n < a\<close> inf_key.simps list.simps(4) neq_Nil_conv not_le order.strict_trans2 sorted2
          takeWhile.simps(1) takeWhile.simps(2))
    ultimately have ?thesis using `n < a` by auto }
  ultimately show ?thesis by auto
qed

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

lemma inf_key_at_most:
  assumes "inf_key ks n = Some k"
  shows "k \<le> n"
  using assms
  by (rule inf_keyE1, metis assms inf_key.simps last_in_set list.simps(4) option.distinct(1)
      set_takeWhileD)

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

lemma inf_key_lt_takeWhile_strict:
  assumes "i < k"
  assumes "sorted ks"
  shows "inf_key ks i = inf_key (takeWhile (\<lambda>n. n < k) ks) i"
  using assms
proof (induction ks)
  case Nil
  then show ?case by auto
next
  case (Cons a ks)
  hence IH: " inf_key ks i = inf_key (takeWhile (\<lambda>n. n < k) ks) i"
    by auto
  have "a \<le> i \<or> i < a" by auto
  moreover
  { assume "a \<le> i"
    hence *: "inf_key (a # ks) i = (if inf_key ks i = None then Some a else inf_key ks i)"
      using inf_key_alt_def[OF `sorted (a # ks)`, of "i"] by auto
    have "takeWhile (\<lambda>n. n < k) (a # ks) = a # takeWhile (\<lambda>n. n < k) ks"
      using `a \<le> i` `i < k` by auto
    moreover have "sorted (a # takeWhile (\<lambda>n. n < k) ks)"
      using `sorted (a # ks)`  by (metis calculation sorted_takeWhile)
    ultimately have "inf_key (takeWhile (\<lambda>n. n < k) (a # ks)) i =
                             (if inf_key (takeWhile (\<lambda>n. n < k) ks) i = None then Some a
                              else inf_key (takeWhile (\<lambda>n. n < k) ks) i)"
      using inf_key_alt_def \<open>a \<le> i\<close> by presburger
    hence ?case using * IH
      by auto }
  moreover
  { assume "i < a"
    hence "inf_key (a # ks) i = None"
      by auto
    hence "inf_key ks i = None"
      using `sorted (a # ks)` by (metis inf_key_alt_def)
    have "takeWhile (\<lambda>n. n < k) (a # ks) = a # takeWhile (\<lambda>n. n < k) ks \<or> takeWhile (\<lambda>n. n < k) (a # ks) = []"
      by auto
    hence "inf_key (takeWhile (\<lambda>n. n < k) (a # ks)) i = None"
      using `i < a` by auto
    with `inf_key (a # ks) i = None` have ?case by auto }
  ultimately show ?case by auto
qed

lemma inf_key_lt_takeWhile:
  assumes "i \<le> k"
  assumes "sorted ks"
  shows "inf_key ks i = inf_key (takeWhile (\<lambda>n. n \<le> k) ks) i"
  using assms
proof (induction ks)
  case Nil
  then show ?case by auto
next
  case (Cons a ks)
  hence IH: "inf_key ks i = inf_key (takeWhile (\<lambda>n. n \<le> k) ks) i"
    by auto
  have "a \<le> i \<or> i < a" by auto
  moreover
  { assume "a \<le> i"
    hence *: "inf_key (a # ks) i = (if inf_key ks i = None then Some a else inf_key ks i)"
      using inf_key_alt_def[OF `sorted (a # ks)`, of "i"] by auto
    have "takeWhile (\<lambda>n. n \<le> k) (a # ks) = a # takeWhile (\<lambda>n. n \<le> k) ks"
      using `a \<le> i` `i \<le> k` by auto
    moreover have "sorted (a # takeWhile (\<lambda>n. n \<le> k) ks)"
      using `sorted (a # ks)`  by (metis calculation sorted_takeWhile)
    ultimately have "inf_key (takeWhile (\<lambda>n. n \<le> k) (a # ks)) i =
                             (if inf_key (takeWhile (\<lambda>n. n \<le> k) ks) i = None then Some a
                              else inf_key (takeWhile (\<lambda>n. n \<le> k) ks) i)"
      using inf_key_alt_def \<open>a \<le> i\<close> by presburger
    hence ?case using * IH
      by auto }
  moreover
  { assume "i < a"
    hence "inf_key (a # ks) i = None"
      by auto
    hence "inf_key ks i = None"
      using `sorted (a # ks)` by (metis inf_key_alt_def)
    have "takeWhile (\<lambda>n. n < k) (a # ks) = a # takeWhile (\<lambda>n. n < k) ks \<or> takeWhile (\<lambda>n. n < k) (a # ks) = []"
      by auto
    hence "inf_key (takeWhile (\<lambda>n. n < k) (a # ks)) i = None"
      using `i < a` by auto
    with `inf_key (a # ks) i = None` have ?case by auto }
  ultimately show ?case by auto
qed

lemma inf_key_less:
  assumes "sorted ks"
  assumes "i \<notin> set ks"
  shows "inf_key ks i = inf_key ks (i - 1)"
proof -
  have f1: "\<forall>ns nsa p pa. (ns \<noteq> nsa \<or> (\<exists>n. (n::nat) \<in> set ns \<and> p n \<noteq> pa n)) \<or> takeWhile p ns = takeWhile pa nsa"
    by (metis (no_types) takeWhile_cong)
  obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> nat" where
    "\<forall>x0 x1 x3. (\<exists>v4. v4 \<in> set x3 \<and> x1 v4 \<noteq> x0 v4) = (nn x0 x1 x3 \<in> set x3 \<and> x1 (nn x0 x1 x3) \<noteq> x0 (nn x0 x1 x3))"
    by moura
  then have f2: "\<forall>ns nsa p pa. (ns \<noteq> nsa \<or> nn pa p ns \<in> set ns \<and> p (nn pa p ns) \<noteq> pa (nn pa p ns)) \<or> takeWhile p ns = takeWhile pa nsa"
    using f1 by presburger
  have "Suc (i - Suc 0) = i \<longrightarrow> nn (\<lambda>n. n \<le> i - 1) (\<lambda>n. n \<le> i) ks \<notin> set ks \<or> (nn (\<lambda>n. n \<le> i - 1) (\<lambda>n. n \<le> i) ks \<le> i) = (nn (\<lambda>n. n \<le> i - 1) (\<lambda>n. n \<le> i) ks \<le> i - 1)"
    by (metis (no_types) One_nat_def assms(2) less_Suc_eq_le less_le)
  then show ?thesis
    using f2 by (metis Suc_pred diff_is_0_eq' inf_key.simps neq0_conv zero_le_one)
qed

lemma inf_key_chopped:
  assumes "sorted ks"
  assumes "\<exists>k' \<in> set ks. k < k' \<and> k' \<le> i"
  shows "inf_key ks i = inf_key (remove1 k ks) i"
proof (cases "k \<in> set ks")
  case True
  then show ?thesis
    using assms
  proof (induction ks)
    case Nil
    then show ?case by auto
  next
    case (Cons a ks)
    hence "k = a \<or> k \<in> set ks \<and> k \<noteq> a"
      by auto
    moreover
    { assume "k = a"
      have "\<exists>k'\<in>set ks. k < k' \<and> k' \<le> i"
        using Cons(4) `k = a` by auto
      hence "inf_key ks i \<noteq> None"
        by (meson Cons.prems(2) inf_key_none leD sorted.simps(2))
      hence "inf_key (a # ks) i = inf_key ks i"
        using inf_key_alt_def[OF `sorted (a # ks)`] by auto
      hence ?case
        using `k = a` by auto }
    moreover
    { assume "k \<in> set ks \<and> k \<noteq> a"
      with Cons have IH: "inf_key ks i = inf_key (remove1 k ks) i" and "k \<noteq> a"
        by auto
      have "inf_key (remove1 k (a # ks)) i = inf_key (a # remove1 k ks) i"
        using `k \<noteq> a` by auto
      also have "... = (if a \<le> i \<and> inf_key (remove1 k ks) i = None then Some a else inf_key (remove1 k ks) i)"
        using sorted_remove1 inf_key_alt_def `sorted (a # ks)`  by (metis \<open>k \<noteq> a\<close> remove1.simps(2))
      finally have *: "inf_key (remove1 k (a # ks)) i =
             (if a \<le> i \<and> inf_key (remove1 k ks) i = None then Some a else inf_key (remove1 k ks) i)"
        by auto
      have "inf_key (a # ks) i = (if a \<le> i \<and> inf_key ks i = None then Some a else inf_key ks i)"
        using inf_key_alt_def[OF `sorted (a # ks)`] by auto
      hence ?case
        using * IH by auto }
    ultimately show ?case by auto
  qed
next
  case False
  then show ?thesis by (simp add: remove1_idem)
qed

lemma inf_key_snoc:
  assumes "t \<le> n"
  assumes "sorted ks"
  assumes "\<forall>k \<in> set ks. k \<le> t"
  shows "inf_key (ks @ [t]) n = Some t"
proof -
  have "\<forall>k \<in> set (ks @ [t]). k \<le> n"
    using assms  by (metis (mono_tags, lifting) Un_insert_right append_Nil2 dual_order.trans
    insert_iff list.simps(15) set_append sorted_append)
  hence "takeWhile (\<lambda>k. k \<le> n) (ks @ [t]) = ks @ [t]"
    using takeWhile_eq_all_conv by auto
  thus ?thesis
    by (simp add: list.case_eq_if)
qed

lemma takeWhile_lt_remove1:
  assumes "sorted xs"
  shows "takeWhile (\<lambda>n. n < t) xs = takeWhile (\<lambda>n. n < t) (remove1 t xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  hence IH: "takeWhile (\<lambda>n. n < t) xs = takeWhile (\<lambda>n. n < t) (remove1 t xs)"
    by auto
  have "t = a \<or> t \<noteq> a" by auto
  moreover
  { assume "t = a"
    hence "remove1 t (a # xs) = xs"
      by auto
    have *: "\<forall>x \<in> set xs. t \<le> x"
      using `sorted (a # xs)` `t = a` less_le by auto
    hence "takeWhile (\<lambda>n. n < t) xs = []"
      by (metis (full_types) Nil_is_append_conv not_le sorted.cases split_list_last
          takeWhile.simps(2) takeWhile_eq_all_conv)
    moreover have "takeWhile (\<lambda>n. n < t) (a # xs) = []"
      using `t = a` * by auto
    ultimately have ?case
      using `remove1 t (a # xs) = xs` by auto }
  moreover
  { assume "t \<noteq> a"
    hence "remove1 t (a # xs) = a # remove1 t xs"
      by auto
    hence ?case
      using IH `t \<noteq> a` by (cases "a < t") (auto) }
  ultimately show ?case by auto
qed

lemma sorted_list_insert:
  assumes "finite K"
  assumes "\<forall>k \<in> K. k < k'"
  shows "sorted_list_of_set (insert k' K) = sorted_list_of_set K @ [k']"
proof -
  have "k' \<notin> K" using assms by auto
  have "sorted_list_of_set (insert k' K) = insort k' (sorted_list_of_set K)"
    using sorted_list_of_set.insert[OF assms(1) `k' \<notin> K`] by auto
  also have "... = sorted_list_of_set K @ [k']"
    using assms by (auto simp add: less_imp_le intro!: sorted_insort_is_snoc)
  finally show ?thesis
    by auto
qed

definition "inf_time \<tau> sig n = inf_key (sorted_list_of_set (keys (\<tau> sig))) n"

lemma inf_time_at_most:
  assumes "inf_time \<tau> sig i = Some k"
  shows "k \<le> i"
  using assms by (simp add: inf_key_at_most inf_time_def)

lemma inf_time_upto_upper_bound_strict:
  assumes "i < k"
  shows "inf_time \<tau> sig i = inf_key (takeWhile (\<lambda>n. n < k) (sorted_list_of_set (keys (\<tau> sig)))) i"
  using assms by (metis inf_key_lt_takeWhile_strict inf_time_def sorted_sorted_list_of_set)

lemma inf_time_upto_upper_bound:
  assumes "i \<le> k"
  shows "inf_time \<tau> sig i = inf_key (takeWhile (\<lambda>n. n \<le> k) (sorted_list_of_set (keys (\<tau> sig)))) i"
  using assms by (metis inf_key_lt_takeWhile inf_time_def sorted_sorted_list_of_set)

lemma inf_time_someE:
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

lemma inf_time_someE2:
  assumes "inf_time \<tau> sig n = Some k"
  shows "k \<in> dom (lookup (\<tau> sig))"
  by (metis assms inf_key_in_list inf_time_def set_keys_dom_lookup)

lemma inf_time_noneE:
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

lemma inf_time_noneI:
  assumes "\<forall>t \<in> dom (lookup (\<tau> sig)). n < t"
  shows "inf_time \<tau> sig n = None"
proof -
  have "set (sorted_list_of_set (keys (\<tau> sig))) = dom (lookup (\<tau> sig))"
    using set_keys_dom_lookup by metis
  hence "\<forall>k\<in>set (sorted_list_of_set (keys (\<tau> sig))). n < k"
    using assms by metis
  hence "inf_key (sorted_list_of_set (keys (\<tau> sig))) n = None"
    by (meson dual_order.strict_trans1 inf_key_at_most inf_key_in_list less_le not_Some_eq)
  thus ?thesis
    unfolding inf_time_def by auto
qed

lemma inf_time_noneE_iff:
  "(\<forall>t \<in> dom (lookup (\<tau> sig)). n < t) \<longleftrightarrow> inf_time \<tau> sig n = None"
  using inf_time_noneE inf_time_noneI by metis

lemma inf_time_noneE2:
  fixes  \<tau> :: "'signal transaction2"
  assumes "inf_time \<tau> sig n = None"
  shows "\<forall>k. k \<le> n \<longrightarrow> lookup (\<tau> sig) k = 0"
  using inf_time_noneE[OF assms] by (metis domIff not_le zero_option_def)

lemma inf_time_neq_t_choice:
  assumes "inf_time (to_transaction2 \<tau>) s i \<noteq> Some t"
  assumes "t \<le> i"
  assumes "t \<in> dom (lookup (to_transaction2 \<tau> s))"
  shows "\<exists>t' > t. inf_time (to_transaction2 \<tau>) s i = Some t'"
proof -
  obtain t' where *: "inf_time (to_transaction2 \<tau>) s i = Some t' \<and> t' \<noteq> t"
    using assms  option.exhaust_sel  by (metis inf_time_noneE leD)
  have "t' > t"
  proof (rule ccontr)
    assume "\<not> t' > t"  hence "t' < t" using * by auto
    have " \<forall>n \<in> dom (lookup (to_transaction2 \<tau> s)). n \<le> i \<longrightarrow> n \<le> t'"
      using * by (auto dest!: inf_time_someE)
    with assms(2-3) `t' < t` show "False" by auto
  qed
  thus ?thesis using * by auto
qed

lemma inf_time_when_lookups_same:
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "inf_time (to_transaction2 \<tau>1) sig n = inf_time (to_transaction2 \<tau>2) sig n"
proof -
  have 0: "\<And>n. n \<le> maxtime \<Longrightarrow> lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
    using lookups_equal_transaction2[OF assms(1)] by auto
  have "inf_time (to_transaction2 \<tau>1) sig n =
        inf_key (takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys (to_transaction2 \<tau>1 sig)))) n"
    using inf_time_upto_upper_bound[OF `n \<le> maxtime`] by auto
  also have "... =
        inf_key (takeWhile (\<lambda>n. n \<le> maxtime) (sorted_list_of_set (keys (to_transaction2 \<tau>2 sig)))) n"
    using takeWhile_lookup_same[OF 0] by auto
  also have "... = inf_time (to_transaction2 \<tau>2) sig n"
    using inf_time_upto_upper_bound[OF `n \<le> maxtime`] by metis
  finally show ?thesis by auto
qed

lemma inf_time_when_lookups_same_strict:
  assumes "\<And>n. n < maxtime \<Longrightarrow> lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
  assumes "n < maxtime"
  shows "inf_time (to_transaction2 \<tau>1) sig n = inf_time (to_transaction2 \<tau>2) sig n"
proof -
  have "inf_time (to_transaction2 \<tau>1) sig n =
        inf_key (takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys (to_transaction2 \<tau>1 sig)))) n"
    using inf_time_upto_upper_bound_strict[OF `n < maxtime`] by auto
  also have "... =
        inf_key (takeWhile (\<lambda>n. n < maxtime) (sorted_list_of_set (keys (to_transaction2 \<tau>2 sig)))) n"
    using takeWhile_lookup_same_strict[OF assms(1)] by auto
  also have "... = inf_time (to_transaction2 \<tau>2) sig n"
    using inf_time_upto_upper_bound_strict[OF `n < maxtime`] by metis
  finally show ?thesis by auto
qed

lemma inf_time_update:
  assumes "\<And>n. t \<le> n \<Longrightarrow> get_trans \<theta> n = 0"
  assumes "Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> = res"
  assumes "t \<le> i"
  shows "inf_time (to_transaction2 res) sig i = Some t"
proof -
  have "to_transaction2 res sig = to_transaction2 (Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta>) sig"
    using `Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> = res` by auto
  also have "... = Poly_Mapping.update t (Some (\<sigma> sig)) (to_transaction2 \<theta> sig)"
    by (auto simp add: to_transaction2_update)
  finally have "to_transaction2 res sig = Poly_Mapping.update t (Some (\<sigma> sig)) (to_transaction2 \<theta> sig)"
    (is "?lhs0 = ?rhs0") by auto
  hence "keys (to_transaction2 res sig) = keys ?rhs0"
    by auto
  also have "... = insert t (keys (to_transaction2 \<theta> sig))"
    by (auto simp add: keys_update zero_option_def)
  finally have "keys (to_transaction2 res sig) = insert t (keys (to_transaction2 \<theta> sig))"
    (is "?lhs1 = ?rhs1") by auto
  have "\<forall>k \<in> keys \<theta>. k < t"
    using `\<And>n. t \<le> n \<Longrightarrow> get_trans \<theta> n = 0` by transfer' auto
  hence "\<forall>k \<in> keys (to_transaction2 \<theta> sig). k < t"
    by (auto simp add: keys_at_most_to_transaction2)
  hence "sorted_list_of_set ?rhs1 = sorted_list_of_set (keys (to_transaction2 \<theta> sig)) @ [t]"
    (is "?lhs2 = ?rhs2") by (meson finite_keys_to_transaction2 sorted_list_insert)
  hence "inf_key ?rhs2 i = Some t"
    using `t \<le> i` by (metis inf_key_snoc list.set_intros(1)  sorted_append sorted_sorted_list_of_set)
  thus ?thesis
    using ` Poly_Mapping.update t (Some \<circ> \<sigma>) \<theta> = res` `?lhs0 = ?rhs0` `?lhs1 = ?rhs1` `?lhs2 = ?rhs2`
    unfolding inf_time_def by auto
qed

lemma lookup_some_inf_time:
  assumes "lookup \<tau> n = Some o \<sigma>"
  shows "inf_time (to_transaction2 \<tau>) sig n = Some n"
proof (rule ccontr)
  have "n \<in> keys (to_transaction2 \<tau> sig)"
    using assms apply transfer' unfolding to_trans_raw2_def by (auto simp add:zero_option_def)
  hence "n \<in> set (sorted_list_of_set (keys (to_transaction2 \<tau> sig)))"
    by auto
  have "sig \<in> dom (lookup \<tau> n)"
    using assms by transfer' auto
  hence n_in: "n \<in> dom (lookup (to_transaction2 \<tau> sig))"
    apply transfer' unfolding to_trans_raw2_def by auto
  assume "inf_time (to_transaction2 \<tau>) sig n \<noteq> Some n"
  then obtain n' where "inf_time (to_transaction2 \<tau>) sig n = None \<or> inf_time (to_transaction2 \<tau>) sig n = Some n' \<and> n' \<noteq> n"
    using option.exhaust_sel by auto
  moreover
  { assume "inf_time (to_transaction2 \<tau>) sig n = None"
    hence *: "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> sig)). n < t"
      by (auto dest!:inf_time_noneE)
    with * have False
      using n_in by auto }
  moreover
  { assume some: "inf_time (to_transaction2 \<tau>) sig n = Some n' \<and> n' \<noteq> n"
    hence "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> sig)). t \<le> n \<longrightarrow> t \<le> n'" and "n' \<noteq> n"
      by( auto dest!: inf_time_someE)
    hence "n \<le> n'"
      using n_in by auto
    with `n' \<noteq> n` have "n < n'"
      by auto
    moreover have "n' \<le> n"
      using some by (auto dest!: inf_time_at_most)
    ultimately have False
      by auto }
  ultimately show False by auto
qed

lemma lookup_some_inf_time':
  assumes "lookup \<tau> n sig = Some (\<sigma> sig)"
  shows "inf_time (to_transaction2 \<tau>) sig n = Some n"
  by (metis assms domI inf_time_at_most inf_time_neq_t_choice not_le order_refl to_trans_raw2_def
      to_transaction2.rep_eq)

lemma inf_time_at_zero:
  assumes "lookup \<tau> 0 = 0"
  shows "inf_time (to_transaction2 \<tau>) sig 0 = None"
proof (rule ccontr)
  assume "inf_time (to_transaction2 \<tau>) sig 0 \<noteq> None"
  then obtain ta where "inf_time (to_transaction2 \<tau>) sig 0 = Some ta"
    by auto
  hence "ta \<in> dom (lookup (to_transaction2 \<tau> sig))" and "ta \<le> 0"
    using inf_time_someE2[OF `inf_time (to_transaction2 \<tau>) sig 0 = Some ta`]
          inf_time_at_most[OF `inf_time (to_transaction2 \<tau>) sig 0 = Some ta`] by auto
  with `lookup \<tau> 0 = 0` show False
    by (transfer', simp add: to_trans_raw2_def domIff zero_fun_def zero_option_def)
qed

lemma inf_time_less:
  assumes "lookup (\<tau> sig) t = 0"
  shows "inf_time \<tau> sig t = inf_time \<tau> sig (t - 1)"
  unfolding inf_time_def using assms inf_key_less by auto

lemma inf_time_someI:
  assumes "k \<in> dom (lookup (\<tau> sig))" and "k \<le> n"
  assumes "\<forall>t \<in> dom (lookup (\<tau> sig)). t \<le> n \<longrightarrow> t \<le> k"
  shows "inf_time \<tau> sig n = Some k"
proof (rule ccontr)
  assume "inf_time \<tau> sig n \<noteq> Some k"
  then obtain k' where "inf_time \<tau> sig n = None \<or> inf_time \<tau> sig n = Some k' \<and> k' \<noteq> k"
    using option.exhaust_sel by auto
  moreover
  { assume "inf_time \<tau> sig n = None"
    hence "\<forall>t \<in> dom (lookup (\<tau> sig)). n < t"
      by (auto dest!: inf_time_noneE)
    with assms(1-2) have "False"  using not_le by blast }
  moreover
  { assume *: "inf_time \<tau> sig n = Some k' \<and> k' \<noteq> k"
    hence "\<forall>t \<in> dom (lookup (\<tau> sig)). t \<le> n \<longrightarrow> t \<le> k'" and "k' \<noteq> k"
      by (auto dest!: inf_time_someE)
    with assms(1-2) have "k < k'"
      by auto
    have "k' \<le> n " and "k' \<in> dom (lookup (\<tau> sig))"
      using * inf_time_at_most   apply fastforce using inf_time_someE2 * by fastforce
    hence "k' \<le> k"
      using assms(3) by auto
    with `k < k'` have False by auto }
  ultimately show "False" by auto
qed

(* Rethink this definition; should @{term "None \<Rightarrow> False"} be removed ? By introducing new type? lifting? *)
definition to_signal :: "'signal transaction2 \<Rightarrow> 'signal \<Rightarrow> time \<Rightarrow> val" where
  "to_signal \<tau> sig t = (case inf_time \<tau> sig t of
                           None    \<Rightarrow> False
                         | Some t' \<Rightarrow> the (lookup (\<tau> sig) t'))"

abbreviation "signal_of \<equiv> to_signal o to_transaction2"

definition to_signal2 :: "val \<Rightarrow> 'signal transaction2 \<Rightarrow> 'signal \<Rightarrow> time \<Rightarrow> val" where
  "to_signal2 def \<tau> sig t = (case inf_time \<tau> sig t of
                              None    \<Rightarrow> def
                            | Some t' \<Rightarrow> the (lookup (\<tau> sig) t'))"

lemma to_signal2_lookup_same:
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "to_signal2 def (to_transaction2 \<tau>1) sig n = to_signal2 def (to_transaction2 \<tau>2) sig n"
proof -
  have "inf_time (to_transaction2 \<tau>1) sig n = inf_time (to_transaction2 \<tau>2) sig n"
    using inf_time_when_lookups_same[OF assms] by auto
  moreover have "\<And>n. n \<le> maxtime \<Longrightarrow> lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
    using lookups_equal_transaction2[OF assms(1)] by auto
  ultimately show ?thesis
    using assms(2) unfolding to_signal2_def by (auto dest!: inf_time_at_most split:option.splits)
qed

abbreviation "signal_of2 def \<equiv> to_signal2 def o to_transaction2"

lemma [simp]:
  "to_transaction2 0 = 0"
  unfolding zero_fun_def apply transfer' unfolding to_trans_raw2_def by (auto simp add: zero_fun_def)

lemma [simp]:
  "inf_time 0 sig t = None"
  unfolding zero_fun_def inf_time_def by auto

lemma signal_of2_empty[simp]:
  "signal_of2 def 0 sig t = def"
  unfolding to_signal2_def comp_def
  apply transfer' unfolding to_trans_raw2_def by auto

lemma signal_of2_zero:
  assumes "lookup \<tau> 0 sig = 0"
  shows "signal_of2 def \<tau> sig 0 = def"
proof -
  have "\<forall>t\<in>dom (lookup (to_transaction2 \<tau> sig)). 0 < t"
    using assms 
    by (metis domIff neq0_conv to_trans_raw2_def to_transaction2.rep_eq zero_option_def)
  hence "inf_time (to_transaction2 \<tau>) sig 0 = None"
    by (intro inf_time_noneI)
  thus ?thesis
    unfolding to_signal2_def comp_def by auto
qed

lemma signal_of2_lookup_same:
  assumes "\<And>n. n \<le> maxtime \<Longrightarrow> lookup \<tau>1 n = lookup \<tau>2 n"
  assumes "n \<le> maxtime"
  shows "signal_of2 def \<tau>1 sig n = signal_of2 def \<tau>2 sig n"
  using to_signal2_lookup_same[OF assms] by auto

lemma signal_of2_lookup_sig_same:
  assumes "\<And>n. lookup (to_transaction2 \<tau>1 sig) n = lookup (to_transaction2 \<tau>2 sig) n"
  shows "signal_of2 def \<tau>1 sig m = signal_of2 def \<tau>2 sig m"
proof -
  have "inf_time (to_transaction2 \<tau>1) sig m = inf_time (to_transaction2 \<tau>2) sig m"
    using inf_time_when_lookups_same assms by (meson inf_time_when_lookups_same_strict less_Suc_eq)
  thus ?thesis
    using assms unfolding to_signal2_def comp_def  by (simp add: option.case_eq_if)
qed

lemma lookup_some_signal_of2:
  assumes "lookup \<tau> n = Some o \<sigma>"
  shows "signal_of2 def \<tau> sig n = \<sigma> sig"
proof -
  have "inf_time (to_transaction2 \<tau>) sig n = Some n"
    using lookup_some_inf_time[OF assms] by auto
  thus ?thesis
    using assms unfolding to_signal2_def comp_def
    by (simp add: to_trans_raw2_def to_transaction2.rep_eq)
qed

lemma lookup_some_signal_of2':
  assumes "lookup \<tau> n sig = Some (\<sigma> sig)"
  shows "signal_of2 def \<tau> sig n = \<sigma> sig"
  using assms
  by (simp add: lookup_some_inf_time' to_signal2_def to_trans_raw2_def to_transaction2.rep_eq)

lemma signal_of2_less:
  assumes "lookup \<tau> t = 0"
  shows "signal_of2 def \<tau> sig t = signal_of2 def \<tau> sig (t - 1)"
proof -
  have " lookup (to_transaction2 \<tau> sig) t = 0"
    using assms by (transfer', auto simp add: to_trans_raw2_def zero_map zero_option_def)
  hence "inf_time (to_transaction2 \<tau>) sig t = inf_time (to_transaction2 \<tau>) sig (t-1)"
    using inf_time_less[of "to_transaction2 \<tau>" "sig"] by auto
  thus ?thesis
    unfolding to_signal2_def comp_def by auto
qed

lemma signal_of2_less_sig:
  assumes "lookup \<tau> t sig = 0"
  shows "signal_of2 def \<tau> sig t = signal_of2 def \<tau> sig (t - 1)"
  by (simp add: assms inf_time_less to_signal2_def to_trans_raw2_def to_transaction2.rep_eq)

lemma signal_of2_less_ind:
  assumes "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> lookup \<tau> n = 0"
  assumes "k1 < k2"
  shows "signal_of2 def \<tau> sig k2 = signal_of2 def \<tau> sig k1"
  using assms
proof (induction "k2")
  case 0
  then show ?case by auto
next
  case (Suc k2)
  hence "get_trans \<tau> (Suc k2) = 0"
    by auto
  hence *: "signal_of2 def \<tau> sig (Suc k2) = signal_of2 def \<tau> sig k2"
    by(auto dest!: signal_of2_less)
  have IH1: "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> get_trans \<tau> n = 0"
    using Suc by auto
  have "k1 < k2 \<or> k1 = k2"
    using `k1 < Suc k2` by auto
  moreover
  { assume IH2: "k1 < k2"
    hence ?case
      using Suc(1)[OF IH1 IH2] * by auto }
  moreover
  { assume "k1 = k2"
    hence ?case using * by auto }
  ultimately show ?case by auto
qed

lemma signal_of2_less_ind':
  assumes "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> lookup \<tau> n sig = 0"
  assumes "k1 < k2"
  shows "signal_of2 def \<tau> sig k2 = signal_of2 def \<tau> sig k1"
  using assms
proof (induction "k2")
  case 0
  then show ?case by auto
next
  case (Suc k2)
  hence "get_trans \<tau> (Suc k2) sig = 0"
    by auto
  hence *: "signal_of2 def \<tau> sig (Suc k2) = signal_of2 def \<tau> sig k2"
    by(auto dest!: signal_of2_less_sig)
  have IH1: "\<And>n. k1 < n \<Longrightarrow> n \<le> k2 \<Longrightarrow> get_trans \<tau> n sig = 0"
    using Suc by auto
  have "k1 < k2 \<or> k1 = k2"
    using `k1 < Suc k2` by auto
  moreover
  { assume IH2: "k1 < k2"
    hence ?case
      using Suc(1)[OF IH1 IH2] * by auto }
  moreover
  { assume "k1 = k2"
    hence ?case using * by auto }
  ultimately show ?case by auto
qed

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
| "beval now \<sigma> \<gamma> \<theta> (Bsig_delayed sig t) = signal_of2 False \<theta> sig (now - t)"
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

lemma lookup_trans_post:
  assumes "s' \<noteq> s"
  shows "lookup (to_transaction2 (trans_post s' v \<tau> k) s) n = lookup (to_transaction2 \<tau> s) n"
  using assms by (transfer', auto simp add:trans_post_raw_def to_trans_raw2_def)

lemma lookup_trans_post_less:
  assumes "n < k"
  shows "lookup (to_transaction2 (trans_post s' v \<tau> k) s) n = lookup (to_transaction2 \<tau> s) n"
  using assms by (transfer', auto simp add:trans_post_raw_def to_trans_raw2_def)

lemma inf_time_trans_post:
  assumes "s' \<noteq> s"
  shows "inf_time (to_transaction2 (trans_post s' v \<tau> k)) s t = inf_time (to_transaction2 \<tau>) s t"
proof -
  have "\<And>n. lookup (to_transaction2 (trans_post s' v \<tau> k) s) n = lookup (to_transaction2 \<tau> s) n"
    by (simp add: lookup_trans_post assms)
  hence "keys (to_transaction2 (trans_post s' v \<tau> k) s) = keys (to_transaction2 \<tau> s)"
    by (metis (full_types) poly_mapping_eqI)
  thus ?thesis
    unfolding inf_time_def by auto
qed

lemma inf_time_trans_post_less:
  assumes "t < k"
  shows "inf_time (to_transaction2 (trans_post s' v \<tau> k)) s t = inf_time (to_transaction2 \<tau>) s t"
proof -
  have "\<And>n. n < k \<Longrightarrow> lookup (to_transaction2 (trans_post s' v \<tau> k) s) n = lookup (to_transaction2 \<tau> s) n"
    by (simp add: lookup_trans_post_less)
  with inf_time_when_lookups_same_strict[OF this `t < k`] show ?thesis
    by auto
qed

lemma signal_of_trans_post:
  assumes "s' \<noteq> s"
  shows "signal_of2 def (trans_post s' v \<tau> k) s t = signal_of2 def \<tau> s t"
  using inf_time_trans_post[OF assms] lookup_trans_post[OF assms]
  unfolding to_signal2_def comp_def  by (simp add: option.case_eq_if)

lemma signal_of_trans_post2:
  assumes "t < k"
  shows "signal_of2 def (trans_post s' v \<tau> k) s t = signal_of2 def \<tau> s t"
  using inf_time_trans_post_less[OF assms] lookup_trans_post_less[OF assms]
  unfolding to_signal2_def comp_def
  by (smt assms case_optionE inf_key_at_most inf_time_def le_less_trans lookup_trans_post_less
      option.case_eq_if option.sel)

lemma signal_of_trans_post3:
  assumes "k \<le> t"
  shows "signal_of2 def (trans_post s v \<tau> k) s t = v"
proof -
  have "inf_time (to_transaction2 (trans_post s v \<tau> k)) s t = Some k"
  proof (rule inf_time_someI)
    show " k \<in> dom (lookup (to_transaction2 (trans_post s v \<tau> k) s))"
      by (transfer', auto simp  add: to_trans_raw2_def trans_post_raw_def)
  next
    show "k \<le> t" using assms by auto
  next
    { fix ta
      assume *: "ta \<in> dom (lookup (to_transaction2 (trans_post s v \<tau> k) s))"
      assume "ta \<le> t"
      have "ta \<le> k"
      proof (rule ccontr)
        assume "\<not> ta \<le> k"
        hence "k < ta" by auto
        hence "lookup (to_transaction2 (trans_post s v \<tau> k) s) ta = None"
          apply transfer' unfolding to_trans_raw2_def trans_post_raw_def by auto
        with * show "False" by auto
      qed }
    thus " \<forall>ta\<in>dom (lookup (to_transaction2 (trans_post s v \<tau> k) s)). ta \<le> t \<longrightarrow> ta \<le> k"
      by auto
  qed
  moreover have "lookup (to_transaction2 (trans_post s v \<tau> k) s) k = Some v"
    apply transfer' unfolding to_trans_raw2_def trans_post_raw_def by auto
  ultimately show ?thesis
    unfolding to_signal2_def comp_def by auto
qed

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

lemma lookup_inr_post_purged:
  assumes "(\<forall>s. s \<in> dom (lookup \<tau> now) \<longrightarrow> \<sigma> s = the (lookup \<tau> now s))"
  shows "\<And>n. now \<le> n \<Longrightarrow> n < now + dly \<Longrightarrow>
                                    lookup (inr_post sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig)
                                  \<or> lookup (inr_post sig val (\<sigma> sig) \<tau> now dly) n sig = None"
proof -
  fix n
  assume "now \<le> n" and "n < now + dly"
  have "is_stable dly \<tau> now sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau> now sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable dly \<tau> now sig (\<sigma> sig)"
    hence "(\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> check (lookup \<tau> m) sig (\<sigma> sig))"
      using is_stable_correct by metis
    hence "\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> (case lookup \<tau> m sig of None \<Rightarrow> True | Some val' \<Rightarrow> \<sigma> sig = val')"
      by auto
    hence "\<forall>m. now < m \<and> m \<le> now + dly \<longrightarrow> lookup \<tau> m sig = None \<or> lookup \<tau> m sig = Some (\<sigma> sig)"
      using option.inject by fastforce
    hence disj: "lookup \<tau> n sig = None \<or> lookup \<tau> n sig = Some (\<sigma> sig)"
      using `now \<le> n` `n < now + dly` using assms by (smt domIff le_eq_less_or_eq option.exhaust_sel)
    have "inr_post sig val (\<sigma> sig) \<tau> now dly = trans_post sig val \<tau> (now + dly)" (is "?inr = ?trans")
      using `is_stable dly \<tau> now sig (\<sigma> sig)` unfolding inr_post_def by auto
    hence "lookup ?inr n sig = lookup ?trans n sig"
      by auto
    also have "... = lookup \<tau> n sig"
      using `n < now + dly` apply transfer' unfolding trans_post_raw_def by auto
    finally have "lookup ?inr n sig = lookup \<tau> n sig"
      by auto
    hence "lookup ?inr n sig = None \<or> lookup ?inr n sig = Some (\<sigma> sig)"
      using disj by auto }
  moreover
  { assume "\<not> is_stable dly \<tau> now sig (\<sigma> sig)"
    hence "inr_post sig val (\<sigma> sig) \<tau> now dly = trans_post sig val (purge dly \<tau> now sig (\<sigma> sig)) (now + dly)"
      (is "?inr = ?trans") unfolding inr_post_def by auto
    hence "lookup ?inr n sig = lookup ?trans n sig"
      by auto
    also have "... = lookup (purge dly \<tau> now sig (\<sigma> sig)) n sig" (is "_ = lookup ?purge n sig")
      using `n < now + dly` apply transfer' unfolding trans_post_raw_def by auto
    finally have "lookup ?inr n sig = lookup ?purge n sig"
      by auto
    moreover have "lookup ?purge n sig = None \<or> lookup ?purge n sig = Some (\<sigma> sig)"
      using purge_correctness' `now \<le> n` `n < now + dly` assms
      by (smt domIff le_eq_less_or_eq option.exhaust_sel purge_before_now_unchanged)
    ultimately have "lookup ?inr n sig = None \<or> lookup ?inr n sig = Some (\<sigma> sig)"
      by auto }
  ultimately show "lookup (inr_post sig val (\<sigma> sig) \<tau> now dly) n sig = Some (\<sigma> sig) \<or>
                   lookup (inr_post sig val (\<sigma> sig) \<tau> now dly) n sig = None"
    by linarith
qed

lemma signal_of_inr_post:
  assumes "now + dly \<le> t"
  shows "signal_of2 def (inr_post s v c \<tau> now dly) s t = v"
proof -
  have "inf_time (to_transaction2 (inr_post s v c \<tau> now dly)) s t = Some (now + dly)"
  proof (rule inf_time_someI)
    show " now + dly \<in> dom (lookup (to_transaction2 (inr_post s v c \<tau> now dly) s))"
      unfolding inr_post_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
      by auto
  next
    show "now + dly \<le> t" using assms by auto
  next
    { fix ta
      assume *: "ta \<in> dom (lookup (to_transaction2 (inr_post s v c \<tau> now dly) s))"
      assume "ta \<le> t"
      have "ta \<le> now + dly"
      proof (rule ccontr)
        assume "\<not> ta \<le> now + dly"
        hence "now + dly < ta" by auto
        hence "lookup (to_transaction2 (inr_post s v c \<tau> now dly) s) ta = None"
          unfolding inr_post_def apply transfer' unfolding trans_post_raw_def to_trans_raw2_def
          by auto
        with * show "False" by auto
      qed }
    thus " \<forall>ta\<in>dom (lookup (to_transaction2 (inr_post s v c \<tau> now dly) s)). ta \<le> t \<longrightarrow> ta \<le> now + dly"
      by auto
  qed
  moreover have "lookup (to_transaction2 (inr_post s v c \<tau> now dly) s) (now + dly) = Some v"
    unfolding inr_post_def apply transfer' unfolding to_trans_raw2_def trans_post_raw_def by auto
  ultimately show ?thesis
    unfolding to_signal2_def comp_def by auto
qed

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

lemma purge_raw_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow> \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> (purge_raw dly \<tau> t sig c) n = 0"
  using assms by (induction dly arbitrary:\<tau>) (auto simp add: Let_def)

lemma purge_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (purge dly \<tau> t sig (\<sigma> sig)) n = 0"
  using assms by (transfer, auto simp add: purge_raw_preserve_trans_removal)

lemma purge_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (purge dly \<tau> t sig c) n = 0"
  using assms by (transfer, auto simp add: purge_raw_preserve_trans_removal')

lemma inr_post_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (inr_post sig x (\<sigma> sig) \<tau> t dly) n = 0"
  using assms  unfolding inr_post_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal)

lemma inr_post_preserve_trans_removal':
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (inr_post sig x c \<tau> t dly) n = 0"
  using assms  unfolding inr_post_def
  by (auto simp add: trans_post_preserve_trans_removal purge_preserve_trans_removal')

lemma signal_of_inr_post2:
  assumes "now \<le> t" and "t < now + dly"
  assumes "\<And>n. n <  now \<Longrightarrow> lookup \<tau> n = 0"
  assumes "(\<forall>s. s \<in> dom (lookup \<tau> now) \<longrightarrow> \<sigma> s = the (lookup \<tau> now s))"
  shows "signal_of2 (\<sigma> s) (inr_post s v (\<sigma> s) \<tau> now dly) s t = (\<sigma> s)"
proof (cases "inf_time (to_transaction2 (inr_post s v (\<sigma> s) \<tau> now dly)) s t = None")
  case True
  then show ?thesis  unfolding to_signal2_def comp_def by auto
next
  case False
  then obtain t' where inf: "inf_time (to_transaction2 (inr_post s v (\<sigma> s) \<tau> now dly)) s t = Some t'"
    by auto
  hence "t' \<le> t" and "t' < now + dly"
    using assms(2) by (auto dest!: inf_time_at_most)
  have *: "\<And>n. n < now \<Longrightarrow> lookup \<tau> n = 0"
    using assms(3) by auto
  have **: "\<And>n. n < now \<Longrightarrow> lookup (inr_post s v (\<sigma> s) \<tau> now dly) n = 0"
    using inr_post_preserve_trans_removal'[OF *] by auto
  have "now \<le> t'"
  proof (rule ccontr)
    assume "\<not> now \<le> t'" hence "t' < now" by auto
    with assms(2) have "lookup (inr_post s v (\<sigma> s) \<tau> now dly) t' = 0"
      using ** by auto
    have "t' \<in> dom (lookup (to_transaction2 (inr_post s v (\<sigma> s) \<tau> now dly) s))"
      using inf_time_someE2[OF inf] by auto
    hence "lookup (inr_post s v (\<sigma> s) \<tau> now dly) t' \<noteq> 0"
      unfolding inr_post_def apply transfer' unfolding to_trans_raw2_def trans_post_raw_def
      by (metis (no_types, lifting) domIff zero_map)
    with `lookup (inr_post s v (\<sigma> s) \<tau> now dly) t' = 0` show False by auto
  qed
  have "t' \<in> dom (lookup (to_transaction2 (inr_post s v (\<sigma> s) \<tau> now dly) s))"
    using inf_time_someE2[OF inf] by auto
  with lookup_inr_post_purged[OF assms(4) `now \<le> t'` `t' < now + dly`]
  have "the (lookup (to_transaction2 (inr_post s v (\<sigma> s) \<tau> now dly) s) t') = (\<sigma> s)"
    by (metis domIff option.sel to_trans_raw2_def to_transaction2.rep_eq)
  with inf show ?thesis unfolding to_signal2_def comp_def by auto
qed

lemma b_seq_exec_preserve_trans_removal:
  assumes "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "\<And>n. n < t \<Longrightarrow> get_trans (b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau>) n = 0"
  using assms
  by (induction ss arbitrary: \<tau>)
     (auto simp add: trans_post_preserve_trans_removal inr_post_preserve_trans_removal)

lemma b_seq_exec_modifies_local:
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_in ss) \<Longrightarrow> i \<ge> t  \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
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
  have "trans_post x1 (beval t \<sigma> \<gamma> \<theta> x2) \<tau> (t + x3) = \<tau>'"
    using Bassign_trans by auto
  thus ?case using `s \<noteq> x1`
    by (transfer', smt fun_upd_apply trans_post_raw_def)
next
  case (Bassign_inert x1 x2 x3)
  hence "s \<noteq> x1" by auto
  have "inr_post x1 (beval t \<sigma> \<gamma> \<theta> x2) (\<sigma> x1) \<tau> t x3 = \<tau>'"
    using Bassign_inert by auto
  then show ?case using `s \<noteq> x1`
    unfolding inr_post_def
    by (transfer', smt fun_upd_apply purge_raw_does_not_affect_other_sig trans_post_raw_def)
next
  case Bnull
  then show ?case by auto
qed

lemma b_seq_exec_modifies_local':
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_in ss) \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using assms
  by (metis b_seq_exec_modifies_local b_seq_exec_preserve_trans_removal not_le)

lemma b_seq_does_not_modify_signals:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_seq_exec t \<sigma> \<gamma> \<theta> ss \<tau> = \<tau>'"
  assumes "s \<notin> set (signals_in ss)"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
proof -
  have "\<And>i. lookup \<tau> i s = lookup \<tau>' i s"
    using b_seq_exec_modifies_local'[OF assms(1-3)] by auto
  hence *: "to_transaction2 \<tau> s = to_transaction2 \<tau>' s"
    by (transfer', auto simp add: to_trans_raw2_def)
  hence "\<And>i. inf_time (to_transaction2 \<tau>) s i = inf_time (to_transaction2 \<tau>') s i"
    unfolding inf_time_def by auto
  hence "\<And>i. to_signal (to_transaction2 \<tau>) s i = to_signal (to_transaction2 \<tau>') s i"
    unfolding to_signal_def by (auto simp add: * split:option.splits)
  thus "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
    by auto
qed

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

lemma clean_zip_same:
  "clean_zip \<tau> \<tau> \<tau> = \<tau>"
  apply transfer' unfolding clean_zip_raw_def by auto

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

definition rem_curr_trans :: "time \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction" where
  "rem_curr_trans t \<tau> = Poly_Mapping.update t 0 \<tau>"

lemma [simp]:
  "rem_curr_trans t empty_trans = empty_trans"
  unfolding rem_curr_trans_def by (transfer, auto)

lemma key_trans2_rem_curr_trans:
  "keys ((to_transaction2 (rem_curr_trans t \<tau>)) s) = keys ((to_transaction2 \<tau>) s) - {t}"
  unfolding rem_curr_trans_def
  by (transfer', auto simp add: zero_fun_def to_trans_raw2_def)

lemma trans_value_same_except_at_removed:
  "\<And>i s. i \<noteq> t \<Longrightarrow>  lookup (to_transaction2                   \<tau>  s) i =
                     lookup (to_transaction2 (rem_curr_trans t \<tau>) s) i"
  unfolding rem_curr_trans_def  apply transfer' unfolding to_trans_raw2_def by auto

lemma inf_time_rem_curr_trans1:
  assumes "inf_time (to_transaction2 \<tau>) s i \<noteq> Some t"
  assumes "t \<in> dom (lookup (to_transaction2 \<tau> s))"
  shows "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i =  inf_time (to_transaction2 \<tau>) s i"
proof (cases "i < t")
  case True
  have "\<And>i s. i < t \<Longrightarrow> inf_time (to_transaction2 \<tau>) s i =
                         inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i"
  proof -
    fix i s
    assume "i < t"
    have "sorted_list_of_set (keys ((to_transaction2 (rem_curr_trans t \<tau>)) s)) =
          remove1 t (sorted_list_of_set (keys ((to_transaction2 \<tau>) s)))"
      (is "?list1 = ?list2")
      using key_trans2_rem_curr_trans[of "t" "\<tau>" "s"]
      sorted_list_of_set_remove[OF finite_keys_to_transaction2, of "\<tau>" "s" "t"]
      by auto
    hence "takeWhile (\<lambda>n. n < t) (sorted_list_of_set (keys ((to_transaction2 \<tau>) s))) =
           takeWhile (\<lambda>n. n < t) ?list2"
      using takeWhile_lt_remove1  sorted_sorted_list_of_set by blast
    hence "takeWhile (\<lambda>n. n < t) (sorted_list_of_set (keys ((to_transaction2 \<tau>) s))) =
          takeWhile (\<lambda>n. n < t) (sorted_list_of_set (keys ((to_transaction2 (rem_curr_trans t \<tau>)) s)))"
      using `?list1 = ?list2` by auto
    thus "inf_time (to_transaction2 \<tau>) s i =
                         inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i"
      using inf_time_upto_upper_bound_strict[OF `i < t`] by metis
  qed
  then show ?thesis using True by auto
next
  case False
  then obtain t' where *: "inf_time (to_transaction2 \<tau>) s i = Some t'" and "t' > t"
    using assms by (meson inf_time_neq_t_choice inf_time_noneE leI)
  hence "i \<ge> t'" and "i > t"
    by (auto dest!:inf_time_at_most)
  hence "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i =
         inf_key (sorted_list_of_set (keys (to_transaction2 (rem_curr_trans t \<tau>) s))) i"
    unfolding inf_time_def by auto
  also have "... = inf_key (remove1 t (sorted_list_of_set (keys ((to_transaction2 \<tau>) s)))) i"
    using key_trans2_rem_curr_trans[of "t" "\<tau>" "s"]
    sorted_list_of_set_remove[OF finite_keys_to_transaction2, of "\<tau>" "s" "t"] by auto
  also have "... = inf_key (sorted_list_of_set (keys ((to_transaction2 \<tau>) s))) i"
    using inf_key_chopped
    by (metis * \<open>t < t'\<close> \<open>t' \<le> i\<close> inf_key_in_list inf_time_def sorted_sorted_list_of_set)
  also have "... = inf_time (to_transaction2 \<tau>) s i"
    unfolding inf_time_def by auto
  finally show ?thesis by auto
qed

lemma inf_time_rem_curr_trans2:
  assumes "inf_time (to_transaction2 \<tau>) s i \<noteq> Some t"
  assumes "t \<notin> dom (lookup (to_transaction2 \<tau> s))"
  shows "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i =  inf_time (to_transaction2 \<tau>) s i"
proof -
  have "to_transaction2 (rem_curr_trans t \<tau>) s = to_transaction2 \<tau> s"
    using assms(2) unfolding rem_curr_trans_def
    apply transfer'
    unfolding to_trans_raw2_def  by (metis domIff fun_upd_apply zero_fun_def zero_option_def)
  thus ?thesis
    by (simp add: inf_time_def)
qed

lemma inf_time_rem_curr_trans:
  assumes "inf_time (to_transaction2 \<tau>) s i \<noteq> Some t"
  shows "inf_time (to_transaction2 (rem_curr_trans t \<tau>)) s i =  inf_time (to_transaction2 \<tau>) s i"
  using assms inf_time_rem_curr_trans1 inf_time_rem_curr_trans2
  by fastforce

lemma inf_time_rem_curr_trans_at_0:
  assumes " inf_time (to_transaction2 \<tau>) sig i = Some 0"
  shows "inf_time (to_transaction2 (rem_curr_trans 0 \<tau>)) sig i = None"
proof -
  have "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> sig)). t \<le> i \<longrightarrow> t \<le> 0"
    using assms by (auto dest!:inf_time_someE)
  hence "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> sig)). 0 < t \<longrightarrow> i < t"
    using not_le by auto
  hence "\<forall>t \<in> dom (lookup (to_transaction2 \<tau> sig)) - {0}. i < t"
    by auto
  moreover have "dom (lookup (to_transaction2 (rem_curr_trans 0 \<tau>) sig)) = dom (lookup (to_transaction2 \<tau> sig)) - {0}"
    unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by (auto simp add: zero_map split:if_splits)
  ultimately have "\<forall>t \<in> dom (lookup (to_transaction2 (rem_curr_trans 0 \<tau>) sig)). i < t"
    by auto
  thus "inf_time (to_transaction2 (rem_curr_trans 0 \<tau>)) sig i = None"
    by (auto intro!: inf_time_noneI)
qed

lemma signal_of2_rem_curr_trans_at_0:
  assumes "\<And>s. s \<in> dom (lookup \<tau> 0) \<Longrightarrow> \<sigma> s = the (lookup \<tau> 0 s)"
  shows "signal_of2 (\<sigma> A) (rem_curr_trans 0 \<tau>) A i = signal_of2 (\<sigma> A) \<tau> A i"
proof (cases "inf_time (to_transaction2 \<tau>) A i = Some 0")
  case True
  hence el: "0 \<in> dom (lookup (to_transaction2 \<tau> A))"
    by (auto dest!: inf_time_someE2)
  hence "signal_of2 (\<sigma> A) \<tau> A i =  the (lookup (to_transaction2 \<tau> A) 0)"
    using True unfolding to_signal2_def comp_def by auto
  also have "... = \<sigma> A"
    using assms el apply transfer' unfolding to_trans_raw2_def by auto
  finally have "signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A"
    by auto
  have "inf_time (to_transaction2 (rem_curr_trans 0 \<tau>)) A i = None"
    using True inf_time_rem_curr_trans_at_0 by metis
  hence "signal_of2 (\<sigma> A) (rem_curr_trans 0 \<tau>) A i = \<sigma> A"
    unfolding to_signal2_def comp_def by auto
  then show ?thesis
    using `signal_of2 (\<sigma> A) \<tau> A i = \<sigma> A` by auto
next
  case False
  have "inf_time (to_transaction2 (rem_curr_trans 0 \<tau>)) A i = inf_time (to_transaction2 \<tau>) A i"
    using inf_time_rem_curr_trans[OF False] by auto
  moreover have "\<And>t'. t' \<noteq> 0 \<Longrightarrow> the (lookup (to_transaction2 (rem_curr_trans 0 \<tau>) A) t') = the (lookup (to_transaction2 \<tau> A) t')"
    unfolding rem_curr_trans_def apply transfer' unfolding to_trans_raw2_def by auto
  ultimately show ?thesis
    using False unfolding to_signal2_def comp_def
    by (metis (no_types, lifting) option.case_eq_if option.distinct(1) option.expand option.sel)
qed


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

lemma b_conc_exec_modifies_local:
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>i s. s \<notin> set (signals_from cs) \<Longrightarrow> i \<ge> t \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using assms
proof (induction cs arbitrary: \<tau> \<tau>')
  case (Bpar cs1 cs2)
  hence "s \<notin> set (signals_from cs1)" and "s \<notin> set (signals_from cs2)"
    by auto
  obtain \<tau>1 \<tau>2 where "b_conc_exec t \<sigma> \<gamma> \<theta> cs1 \<tau> = \<tau>1" and \<tau>2_def: "b_conc_exec t \<sigma> \<gamma> \<theta> cs2 \<tau> = \<tau>2"
    and \<tau>'_def: "\<tau>' = clean_zip \<tau> \<tau>1 \<tau>2"
    using Bpar(5) by auto
  hence "lookup \<tau> i s = lookup \<tau>1 i s"
    using Bpar `s \<notin> set (signals_from cs1)` by blast
  moreover have "lookup \<tau> i s = lookup \<tau>2 i s"
    using \<tau>2_def `s \<notin> set (signals_from cs2)` Bpar(2) `i \<ge> t` by blast
  ultimately have "lookup \<tau> i s = lookup (clean_zip \<tau> \<tau>1 \<tau>2) i s"
    by (transfer', smt clean_zip_raw_def map_add_None map_add_dom_app_simps(1)
        map_add_dom_app_simps(3)  map_diff_def)
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

lemma b_conc_exec_modifies_local':
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  shows "\<And>s. s \<notin> set (signals_from cs) \<Longrightarrow> lookup \<tau> i s = lookup \<tau>' i s"
  using assms
  by (metis b_conc_exec_modifies_local b_conc_exec_preserve_trans_removal not_le)

lemma b_conc_exec_does_not_modify_signals:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  assumes "s \<notin> set (signals_from cs)"
  shows "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
proof -
  have "\<And>i. lookup \<tau> i s = lookup \<tau>' i s"
    using b_conc_exec_modifies_local'[OF assms(1-3)] by auto
  hence *: "to_transaction2 \<tau> s = to_transaction2 \<tau>' s"
    by (transfer', auto simp add: to_trans_raw2_def)
  hence "\<And>i. inf_time (to_transaction2 \<tau>) s i = inf_time (to_transaction2 \<tau>') s i"
    unfolding inf_time_def by auto
  hence "\<And>i. to_signal (to_transaction2 \<tau>) s i = to_signal (to_transaction2 \<tau>') s i"
    unfolding to_signal_def by (auto simp add: * split:option.splits)
  thus "\<And>i. signal_of \<tau> s i = signal_of \<tau>' s i"
    by auto
qed

lemma b_conc_exec_empty_event:
  assumes "t, \<sigma>, {}, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  shows "\<tau> = \<tau>'"
  using assms
proof (induction cs arbitrary:\<tau>')
  case (Bpar cs1 cs2)
  then obtain tau1 tau2 where "tau1 = b_conc_exec t \<sigma> {} \<theta> cs1 \<tau>" and "tau2 = b_conc_exec t \<sigma> {} \<theta> cs2 \<tau>"
    and *: "\<tau>' = clean_zip \<tau> tau1 tau2" by auto
  with Bpar have "tau1 = \<tau>" and "tau2 = \<tau>" by presburger+
  hence "\<tau>' = \<tau>" using * clean_zip_same by auto
  thus ?case by auto
next
  case (Bsingle x1 x2)
  then show ?case by auto
qed

fun disjnts where
  "disjnts \<gamma> (Bsingle sl ss) \<longleftrightarrow> disjnt \<gamma> sl"
| "disjnts \<gamma> (Bpar cs1 cs2) \<longleftrightarrow> disjnts \<gamma> cs1 \<and> disjnts \<gamma> cs2"

lemma b_conc_exec_disjnts_event:
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
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

subsubsection \<open>Semantics of simulation\<close>

text \<open>The other aspect of the semantics is how to simulate, or in a sense execute, VHDL text. One
has to deal with the advance of simulation time. Rather than advancing time naturally, the simulation
proceeds to the "next interesting point of computation" @{cite "VanTassel1995"}. The following
function does exactly this purpose.\<close>

definition next_time :: "time \<Rightarrow> 'signal transaction \<Rightarrow> time" where
  "next_time t \<tau>' = (if \<tau>' = 0 then t else LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"

lemma next_time_lookup_zero:
  "\<forall>n. t < n \<and> n < next_time t \<tau>' \<longrightarrow> lookup \<tau>' n = 0"
proof -
  have f1: "dom (0::'a \<Rightarrow> bool option) = {}"
    by (simp add: zero_fun_def zero_option_def)
  obtain nn :: nat where
    "(\<exists>v0. (t < v0 \<and> v0 < next_time t \<tau>') \<and> get_trans \<tau>' v0 \<noteq> 0) = ((t < nn \<and> nn < next_time t \<tau>') \<and> get_trans \<tau>' nn \<noteq> 0)"
    by moura
  moreover
  { assume "get_trans \<tau>' nn \<noteq> Map.empty"
    then have "\<not> nn < (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
      using not_less_Least by auto
    then have "(\<not> t < nn \<or> \<not> nn < next_time t \<tau>') \<or> get_trans \<tau>' nn = 0"
      by (metis (no_types) less_trans nat_neq_iff next_time_def) }
  ultimately show ?thesis
    using f1 by auto
qed


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

lemma signal_of2_init:
  assumes "t \<le> i"
  assumes "i < next_time t \<tau>'"
  assumes "s \<in> dom (lookup \<tau>' t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>' t s)"
  assumes *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
  shows "signal_of2 (\<sigma> s) \<tau>' s i = \<sigma> s"
proof -
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *] by auto
  obtain t' where "inf_time (to_transaction2 \<tau>') s i = Some t' \<or> inf_time (to_transaction2 \<tau>') s i = None"
    by auto
  moreover
  { assume "inf_time (to_transaction2 \<tau>') s i = None"
    hence "signal_of2 (\<sigma> s) \<tau>' s i = \<sigma> s"
      unfolding to_signal2_def comp_def by auto }
  moreover
  { assume "inf_time (to_transaction2 \<tau>') s i = Some t'"
    hence "t' < next_time t \<tau>'"
      using inf_time_upto_upper_bound_strict[OF assms(2), of "to_transaction2 \<tau>'" "s" ]
      by (meson assms(2) inf_time_at_most order.strict_trans1)
    have "t' \<in> dom (lookup (to_transaction2 \<tau>' s))"
      using inf_time_someE2[OF `inf_time (to_transaction2 \<tau>') s i = Some t'`] by auto
    hence "lookup \<tau>' t' \<noteq> 0"
      apply transfer' unfolding to_trans_raw2_def zero_fun_def zero_option_def by auto
    have **: "\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 \<tau>' s) n = 0"
      using * apply transfer' unfolding to_trans_raw2_def  by (simp add: zero_fun_def)
    have "t \<le> t'"
    proof (rule ccontr)
      assume "\<not> t \<le> t'" hence "t' < t" by auto
      with ** have "lookup (to_transaction2 \<tau>' s) t' = 0" by auto
      with `t' \<in> dom (lookup (to_transaction2 \<tau>' s))` show False
        apply transfer' unfolding to_trans_raw2_def by (simp add: domIff zero_option_def)
    qed
    moreover have "\<And>n. t < n \<Longrightarrow> n < next_time t \<tau>' \<Longrightarrow> lookup \<tau>' t = 0"
      using next_time_at_least2 order.strict_trans by blast
    ultimately have "t' = t"
      using `t' < next_time t \<tau>'` `lookup \<tau>' t' \<noteq> 0`  by (simp add: next_time_at_least2)
    hence "inf_time (to_transaction2 \<tau>') s i = Some t"
      using `inf_time (to_transaction2 \<tau>') s i = Some t'` by auto
    hence "signal_of2 (\<sigma> s) \<tau>' s i = \<sigma> s"
      using assms(3) unfolding to_signal2_def comp_def
      using \<open>get_trans \<tau>' t' \<noteq> 0\<close> \<open>t' < next_time t \<tau>'\<close> next_time_at_least2 by blast }
  ultimately show "signal_of2 (\<sigma> s) \<tau>' s i = \<sigma> s"
    by auto
qed

lemma next_time_eq_next_rem_curr_trans:
  assumes "next_time t \<tau> \<noteq> t"
  assumes *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "next_time t \<tau> = next_time t (rem_curr_trans t \<tau>)"
proof -
  have "\<tau> \<noteq> 0"
    using assms by auto
  hence "(LEAST n. dom (lookup \<tau> n) \<noteq> {}) \<noteq> t"
    using assms unfolding next_time_def by auto
  hence "lookup \<tau> t = 0"
    using assms  by (metis le_neq_trans next_time_at_least next_time_at_least2)
  hence "rem_curr_trans t \<tau> = \<tau>"
    unfolding rem_curr_trans_def  by (metis lookup_update poly_mapping_eqI)
  thus ?thesis by auto
qed

lemma signal_of2_init':
  assumes "t \<le> i"
  assumes "i < next_time t (rem_curr_trans t \<tau>)"
  assumes "s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
  assumes *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
  shows "signal_of2 (\<sigma> s) \<tau> s i = \<sigma> s"
proof -
  have "t \<le> next_time t \<tau>"
    using next_time_at_least[OF *] by auto
  have "\<And>n. n < t \<Longrightarrow> get_trans (rem_curr_trans t \<tau>) n = 0"
    using * unfolding rem_curr_trans_def by transfer' auto
  hence "t \<le> next_time t (rem_curr_trans t \<tau>)"
    using next_time_at_least by metis
  obtain t' where "inf_time (to_transaction2 \<tau>) s i = Some t' \<or> inf_time (to_transaction2 \<tau>) s i = None"
    by auto
  moreover
  { assume "inf_time (to_transaction2 \<tau>) s i = None"
    hence "signal_of2 (\<sigma> s) \<tau> s i = \<sigma> s"
      unfolding to_signal2_def comp_def by auto }
  moreover
  { assume "inf_time (to_transaction2 \<tau>) s i = Some t'"
    hence "t' < next_time t (rem_curr_trans t \<tau>)"
      using inf_time_upto_upper_bound_strict[OF assms(2), of "to_transaction2 \<tau>" "s" ]
      by (meson assms(2) inf_time_at_most order.strict_trans1)
    have "t' \<in> dom (lookup (to_transaction2 \<tau> s))"
      using inf_time_someE2[OF `inf_time (to_transaction2 \<tau>) s i = Some t'`] by auto
    hence "lookup \<tau> t' \<noteq> 0"
      apply transfer' unfolding to_trans_raw2_def zero_fun_def zero_option_def by auto
    have **: "\<And>n. n < t \<Longrightarrow> lookup (to_transaction2 \<tau> s) n = 0"
      using * apply transfer' unfolding to_trans_raw2_def  by (simp add: zero_fun_def)
    have "t \<le> t'"
    proof (rule ccontr)
      assume "\<not> t \<le> t'" hence "t' < t" by auto
      with ** have "lookup (to_transaction2 \<tau> s) t' = 0" by auto
      with `t' \<in> dom (lookup (to_transaction2 \<tau> s))` show False
        apply transfer' unfolding to_trans_raw2_def by (simp add: domIff zero_option_def)
    qed
    hence "next_time t (rem_curr_trans t \<tau>) \<noteq> t"
      using `t' < next_time t (rem_curr_trans t \<tau>)` by auto
    hence "t < next_time t (rem_curr_trans t \<tau>)"
      using `t \<le> next_time t (rem_curr_trans t \<tau>)` by auto
    have h: "\<And>n. t < n \<Longrightarrow> n < next_time t (rem_curr_trans t \<tau>) \<Longrightarrow> lookup (rem_curr_trans t \<tau>) n = 0"
      using next_time_at_least2 order.strict_trans  by blast
    have h0: "\<And>n. t < n \<Longrightarrow> n < next_time t (rem_curr_trans t \<tau>) \<Longrightarrow> next_time t \<tau> \<noteq> t \<Longrightarrow> lookup \<tau> n = 0"
    proof (rule ccontr)
      fix n
      assume "t < n"
      assume "n < next_time t (rem_curr_trans t \<tau>)"
      assume "next_time t \<tau> \<noteq> t"
      assume "lookup \<tau> n \<noteq> 0"
      hence "dom (lookup \<tau> n) \<noteq> {}"
        by (metis (no_types, hide_lams) dom_eq_empty_conv map_add_subsumed1 map_add_subsumed2
            map_le_def zero_map)
      hence "next_time t \<tau> \<le> n"
        unfolding next_time_def using `t < n`  by (simp add: Least_le)
      have "next_time t \<tau> = next_time t (rem_curr_trans t \<tau>)"
          using "*" \<open>next_time t \<tau> \<noteq> t\<close> next_time_eq_next_rem_curr_trans by auto
      hence "next_time t (rem_curr_trans t \<tau>) \<le> n"
          using `next_time t \<tau> \<le> n` by auto
      with `n < next_time t (rem_curr_trans t \<tau>)` show "False" by auto
    qed
    have h0': "\<And>n. t < n \<Longrightarrow> n < next_time t (rem_curr_trans t \<tau>) \<Longrightarrow> next_time t \<tau> = t \<Longrightarrow> lookup \<tau> n = 0"
    proof -
      fix n
      assume "t < n"
      assume "n < next_time t (rem_curr_trans t \<tau>)"
      assume "next_time t \<tau> = t"
      hence "\<tau> = 0 \<or> (LEAST n. dom (lookup \<tau> n) \<noteq> {}) = t"
        unfolding next_time_def by metis
      moreover
      { assume "\<tau> = 0"
        hence "rem_curr_trans t \<tau> = \<tau>"
          unfolding rem_curr_trans_def  using \<open>get_trans \<tau> t' \<noteq> 0\<close> by auto
        hence "lookup \<tau> n = 0" using h[OF `t < n`] `n < next_time t (rem_curr_trans t \<tau>)`
          by auto }
      moreover
      { assume "(LEAST n. dom (lookup \<tau> n) \<noteq> {}) = t"
        hence "get_trans (rem_curr_trans t \<tau>) n = 0"
          using h[OF `t < n` `n < next_time t (rem_curr_trans t \<tau>)`] by auto
        have "lookup (rem_curr_trans t \<tau>) n = lookup \<tau> n"
          using `t < n` unfolding rem_curr_trans_def by transfer' auto
        hence "lookup \<tau> n = 0"
          using `lookup (rem_curr_trans t \<tau>) n = 0` by auto }
      ultimately  show "lookup \<tau> n = 0"
        by auto
    qed
    hence h1: "\<And>n. t < n \<Longrightarrow> n < next_time t (rem_curr_trans t \<tau>)  \<Longrightarrow> lookup \<tau> n = 0"
      using h0 h0' by auto
    hence "t' = t"
      using `t \<le> t'` `t' < next_time t (rem_curr_trans t \<tau>)` `lookup \<tau> t' \<noteq> 0` le_neq_trans
      by blast
    hence "inf_time (to_transaction2 \<tau>) s i = Some t"
      using `inf_time (to_transaction2 \<tau>) s i = Some t'` by auto
    have "s \<in> dom (get_trans \<tau> t)"
      using inf_time_someE2[OF `inf_time (to_transaction2 \<tau>) s i = Some t`]
      apply transfer' unfolding to_trans_raw2_def by auto
    hence "the (lookup (to_transaction2 \<tau> s) t) = \<sigma> s"
      using assms(3)[OF `s \<in> dom (get_trans \<tau> t)`] apply transfer' unfolding to_trans_raw2_def by auto
    hence "signal_of2 (\<sigma> s) \<tau> s i = \<sigma> s"
      using `inf_time (to_transaction2 \<tau>) s i = Some t` unfolding to_signal2_def comp_def
      by auto }
  ultimately show "signal_of2 (\<sigma> s) \<tau> s i = \<sigma> s"
    by auto
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

definition add_to_beh :: "'signal state \<Rightarrow> 'signal trace \<Rightarrow> time \<Rightarrow> time \<Rightarrow> 'signal trace" where
  "add_to_beh \<sigma> \<theta> st fi = (if st < fi then Poly_Mapping.update st (Some o \<sigma>) \<theta> else \<theta>)"

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
                        add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> res)
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
                        add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> beh)"
  using bau[OF assms(4)] assms by auto

lemma case_bau2:
  assumes "t \<le> maxtime"
  assumes "\<not> quiet \<tau> \<gamma>"
  assumes "(maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh)"
  obtains \<tau>' where "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'" and
                   "(maxtime,
                       next_time t \<tau>',
                          next_state t \<tau>' \<sigma>,
                              next_event t \<tau>' \<sigma>,
                                  add_to_beh \<sigma> \<theta> t (next_time t \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> beh)"
  using bau[OF assms(3)] assms by auto

lemma beh_res:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> beh"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "t \<le> maxtime"
  shows "\<And>n. n < t \<Longrightarrow> lookup \<theta> n = lookup beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have *: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF 1(7)] 1(3) by auto
  have "t \<le> next_time t \<tau>'"
    using next_time_at_least[OF *, of "t"] by auto
  hence ind1: "n < next_time t \<tau>'"
    using `n < t` by auto
  have ind2: "(\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans \<tau>' n = 0) "
    by (simp add: next_time_at_least2)
  have "next_time t \<tau>' \<le> maxtime \<or> \<not> next_time t \<tau>' \<le> maxtime"
    by auto
  moreover
  { assume ind3: "next_time t \<tau>' \<le> maxtime"
    with 1(5)[OF ind1 ind2] have "get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) n = get_trans res n"
      by auto
    hence ?case using `n < t`
      unfolding add_to_beh_def apply transfer' by (metis (full_types) fun_upd_apply nat_neq_iff) }
  moreover
  { assume "\<not> next_time t \<tau>' \<le> maxtime" hence "maxtime < next_time t \<tau>'" by auto
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
      using `t \<le> maxtime` unfolding add_to_beh_def by auto
    define \<sigma>' where "\<sigma>' = next_state t \<tau>' \<sigma>"
    define \<gamma>' where "\<gamma>' = next_event t \<tau>' \<sigma>"
    define \<theta>' where "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"
    hence \<theta>'_def2: "\<theta>' = Poly_Mapping.update t (Some o \<sigma>) \<theta>"
      using `add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = Poly_Mapping.update t (Some o \<sigma>) \<theta>` by auto
    hence "maxtime, next_time t \<tau>', \<sigma>', \<gamma>', \<theta>' \<turnstile> <cs, \<tau>'> \<leadsto> res"
      using 1(4) unfolding \<theta>'_def \<sigma>'_def \<gamma>'_def by auto
    hence "res = override_lookups_on_open_left \<theta>' 0 maxtime (next_time t \<tau>')"
      using case_timesup[OF `\<not> next_time t \<tau>' \<le> maxtime`] by metis
    hence ?case
      unfolding \<theta>'_def2 using `n < t` `t \<le> maxtime` `maxtime < next_time t \<tau>'`
      by transfer' auto }
  ultimately  show ?case
    by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  then show ?case  by (metis lookup_update not_le order_refl)
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case by auto
qed

lemma borderline_big_step:
  assumes "maxtime, t', \<sigma>', \<gamma>', \<theta>' \<turnstile> <cs, \<tau>'> \<leadsto> beh"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t \<le> maxtime" and "maxtime < t'"
  assumes "\<And>n. t < n \<Longrightarrow> lookup \<theta> n = 0"
  assumes "\<theta>' = add_to_beh \<sigma> \<theta> t t'"
  shows "\<And>n. n \<le> t' \<Longrightarrow> lookup \<theta>' n = lookup beh n"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  then show ?case by auto
next
case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  then show ?case by auto
next
  case (3 t' maxtime \<theta>' res \<sigma>' \<gamma>' cs \<tau>')
  have "n \<le> maxtime \<or> maxtime < n" by auto
  moreover
  { assume "n \<le> maxtime"
    hence "lookup res n = lookup \<theta>' n"
      using 3(2) by transfer' auto
    hence ?case by auto }
  moreover
  { assume "maxtime < n"
    hence "lookup res n = 0"
      using 3(2) `n \<le> t'` by transfer' auto
    have "lookup \<theta>' n = lookup \<theta> n"
      using 3(8) `t \<le> maxtime` `maxtime < t'` unfolding add_to_beh_def using `maxtime < n`
      by transfer' auto
    also have "... = 0"
      using 3(7) `maxtime < n` `t \<le> maxtime` by auto
    finally have "lookup \<theta>' n = 0"
      by auto
    with `lookup res n = 0` have ?case by auto }
  ultimately show ?case by auto
qed

lemma beh_and_res_same_until_now:
  assumes "maxtime, t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, \<tau>> \<leadsto> res"
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  shows "\<And>i. i < t \<Longrightarrow> i \<le> maxtime \<Longrightarrow> lookup \<theta> i = lookup res i"
  using assms
proof (induction rule:b_simulate_fin.induct)
  case (1 t maxtime \<tau> \<gamma> \<sigma> \<theta> cs \<tau>' res)
  have "i < next_time t \<tau>"
    using `i < t` next_time_at_least[OF 1(8), of "t"] by auto
  moreover have "i \<le> maxtime"
    using `i < t` `t \<le> maxtime` by auto
  moreover have "\<And>n. n < next_time t \<tau>' \<Longrightarrow> get_trans \<tau>' n = 0"
  proof -
    fix n
    assume "n < next_time t \<tau>'"
    hence "n < t \<or> t \<le> n \<and> n < next_time t \<tau>'"
      by auto
    moreover
    { assume "n < t"
      hence "get_trans \<tau>' n = 0"
        using b_conc_exec_rem_curr_trans_preserve_trans_removal[OF 1(8), of "t"] 1(3)
        by auto }
    moreover
    { assume "t \<le> n \<and> n < next_time t \<tau>'"
      have "\<tau>' = 0 \<or> \<tau>' \<noteq> 0" by auto
      moreover
      { assume "\<tau>' = 0"
        hence "next_time t \<tau>' = t" by auto
        hence "False"
          using `t \<le> n \<and> n < next_time t \<tau>'` by auto
        hence "get_trans \<tau>' n = 0"
          by auto }
      moreover
      { assume "\<tau>' \<noteq> 0"
        hence "next_time t \<tau>' = (LEAST n. dom (get_trans \<tau>' n) \<noteq> {})"
          unfolding next_time_def by auto
        with `t \<le> n \<and> n < next_time t \<tau>'` have "get_trans \<tau>' n = 0"
          using next_time_at_least2 by blast }
      ultimately have "get_trans \<tau>' n = 0" by blast
    }
    ultimately show "get_trans \<tau>' n = 0" by blast
  qed
  ultimately have IH: "get_trans (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) i = get_trans res i"
    using 1(5)[of "i"]  by (metis (full_types) "1.hyps"(3) "1.prems"(1) "1.prems"(3)
    b_conc_exec_rem_curr_trans_preserve_trans_removal next_time_at_least order.strict_trans2)
  have "t < next_time t \<tau>' \<or> \<not> t < next_time t \<tau>'"
    by auto
  moreover
  { assume "t < next_time t \<tau>'"
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') =  Poly_Mapping.update t (Some o \<sigma>) \<theta>"
      unfolding add_to_beh_def by auto
    hence ?case
      using IH `i < t` by (simp add: lookup_update) }
  moreover
  { assume "\<not> t < next_time t \<tau>'"
    hence "add_to_beh \<sigma> \<theta> t (next_time t \<tau>') = \<theta>"
      unfolding add_to_beh_def by auto
    hence ?case
      using IH by auto }
  ultimately show ?case by auto
next
  case (2 t maxtime \<tau> \<gamma> \<sigma> \<theta> res cs)
  then show ?case
    by transfer' auto
next
  case (3 t maxtime \<theta> res \<sigma> \<gamma> cs \<tau>)
  then show ?case
    by transfer' auto
qed

lemma b_conc_exec_does_not_modify_signals2:
  assumes "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
  assumes "b_conc_exec t \<sigma> \<gamma> \<theta> cs \<tau> = \<tau>'"
  assumes "s \<notin> set (signals_from cs)"
  shows   "\<And>i. next_time t \<tau>' \<le> i \<Longrightarrow> signal_of2 (\<sigma> s) \<tau> s i = signal_of2 (next_state t \<tau>' \<sigma> s) \<tau>' s i"
proof -
  have lookup_same: "\<And>i. lookup \<tau> i s = lookup \<tau>' i s"
    using b_conc_exec_modifies_local'[OF assms(1-3)] by auto
  hence *: "to_transaction2 \<tau> s = to_transaction2 \<tau>' s"
    by (transfer', auto simp add: to_trans_raw2_def)
  hence **: "\<And>i. inf_time (to_transaction2 \<tau>) s i = inf_time (to_transaction2 \<tau>') s i"
    unfolding inf_time_def by auto

  fix i
  assume "next_time t \<tau>' \<le> i"
  { assume "inf_time (to_transaction2 \<tau>') s i = None"
    hence "\<forall>k. k \<le> i \<longrightarrow> lookup (to_transaction2 \<tau>' s) k = 0"
      by (auto dest!: inf_time_noneE2)
    hence 0: "lookup (to_transaction2 \<tau>' s) (next_time t \<tau>') = 0"
      using `next_time t \<tau>' \<le> i` by auto
    have "next_state t \<tau>' \<sigma> s = \<sigma> s"
    proof -
      define t' where "t' = next_time t \<tau>'"
      define m where "m = lookup \<tau>' t'"
      hence **: "next_state t \<tau>' \<sigma> s = override_on \<sigma> (the o m) (dom m) s"
        unfolding next_state_def t'_def m_def Let_def by auto
      have "s \<notin> dom m"
        using 0 unfolding t'_def[THEN sym] m_def apply transfer' unfolding to_trans_raw2_def
        by (simp add: domIff zero_option_def)
      thus "next_state t \<tau>' \<sigma> s = \<sigma> s"
        unfolding ** by auto
    qed }
  note case_none = this
  have "to_signal2 (\<sigma> s) (to_transaction2 \<tau>) s i =
                                           to_signal2 (next_state t \<tau>' \<sigma> s) (to_transaction2 \<tau>') s i"
    using ** case_none unfolding to_signal2_def  by (auto simp add: * split:option.splits)
  thus "signal_of2 (\<sigma> s) \<tau> s i = signal_of2 (next_state t \<tau>' \<sigma> s) \<tau>' s i"
    by auto
qed

definition context_invariant :: "nat \<Rightarrow> 'signal state \<Rightarrow> 'signal event \<Rightarrow> 'signal transaction \<Rightarrow> 'signal transaction \<Rightarrow> bool" where
  "context_invariant t \<sigma> \<gamma> \<theta> \<tau> \<equiv> (\<forall>n. n < t \<longrightarrow> lookup \<tau> n = 0)
                               \<and> (\<gamma> = {s. \<sigma> s \<noteq> signal_of2 False \<theta> s (t - 1)})
                               \<and> (\<forall>s. s \<in> dom (lookup \<tau> t) \<longrightarrow> \<sigma> s = the (lookup \<tau> t s))
                               \<and> (\<forall>n. t \<le> n \<longrightarrow> lookup \<theta> n = 0)"

lemma trans_degree_gt_t:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>" and "\<tau> \<noteq> 0"
  shows "t < Poly_Mapping.degree \<tau>"
proof (rule ccontr)
  assume "\<not> t < Poly_Mapping.degree \<tau>"
  hence "Poly_Mapping.degree \<tau> \<le> t" by auto
  have "Poly_Mapping.degree \<tau> = 0 \<or> 0 < Poly_Mapping.degree \<tau>"
    by auto
  moreover
  { assume gt: "0 < Poly_Mapping.degree \<tau>"
    hence "lookup \<tau> (Poly_Mapping.degree \<tau> - 1) \<noteq> 0"
      using degree_greater_zero_in_keys[OF gt] by auto
    with `context_invariant t \<sigma> \<gamma> \<theta> \<tau>` have "False"
      unfolding context_invariant_def  using \<open>\<not> t < Poly_Mapping.degree \<tau>\<close>  using gt by auto }
  moreover
  { assume "Poly_Mapping.degree \<tau> = 0"
    hence "\<tau> = 0" using degree_zero_iff by auto
    with `\<tau> \<noteq> 0` have "False"
      by auto }
  ultimately show "False" 
    by auto
qed

lemma context_invariant:
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <cs, rem_curr_trans t \<tau>> \<longrightarrow>\<^sub>c \<tau>'"
  assumes "t < next_time t \<tau>'"
  shows "context_invariant (next_time t \<tau>') (next_state t \<tau>' \<sigma>) (next_event t \<tau>' \<sigma>) (add_to_beh \<sigma> \<theta> t (next_time t \<tau>')) \<tau>'"
proof -
  have 0: "\<And>n. n < t \<Longrightarrow> get_trans \<tau> n = 0"
    using assms unfolding context_invariant_def by auto
  hence 1: "\<And>n. n < t \<Longrightarrow> get_trans \<tau>' n = 0"
    using b_conc_exec_rem_curr_trans_preserve_trans_removal assms(2) by metis
  have 2: "\<And>n. t \<le> n \<Longrightarrow> lookup \<theta> n = 0"
    using assms unfolding context_invariant_def by auto

  define t' where t'_def: "t' = next_time t \<tau>'"
  define \<sigma>' where \<sigma>'_def: "\<sigma>' = next_state t \<tau>' \<sigma>"
  define \<gamma>' where \<gamma>'_def: "\<gamma>' = next_event t \<tau>' \<sigma>"
  define \<theta>' where \<theta>'_def: "\<theta>' = add_to_beh \<sigma> \<theta> t (next_time t \<tau>')"

  have " t \<le> next_time t \<tau>'"
    using assms(3) by auto
  have 3: "\<forall>n. n < t' \<longrightarrow> lookup \<tau>' n = 0"
    using next_time_at_least2 t'_def by metis
  have 4: "\<forall>n. t' \<le> n \<longrightarrow> lookup \<theta>' n = 0"
    unfolding \<theta>'_def add_to_beh_def t'_def using 2 `t \<le> next_time t \<tau>'`
    by transfer' auto
  have 5: "\<forall>s. s \<in> dom (lookup \<tau>' t') \<longrightarrow> \<sigma>' s = the (lookup \<tau>' t' s)"
    unfolding \<sigma>'_def next_state_def t'_def Let_def comp_def by auto
  have "\<And>s. signal_of2 False \<theta>' s (t' - 1) = \<sigma> s"
  proof -
    have "t' - 1 = t \<or> t < t' - 1"
      using assms(3) unfolding t'_def by auto
    moreover
    { assume "t' - 1 = t"
      have "lookup \<theta>' t = Some o \<sigma>"
        unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'`  by transfer' auto
      hence "\<And>s. signal_of2 False \<theta>' s (t' - 1) = \<sigma> s"
        using lookup_some_signal_of2 `t' - 1 = t` by metis }
    moreover
    { assume "t < t' - 1"
      have "\<And>n. t < n \<Longrightarrow> n \<le> t' - 1 \<Longrightarrow> get_trans \<theta>' n = 0"
        unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'` unfolding t'_def
        using 2  by (simp add: lookup_update)
      hence "\<And>s. signal_of2  False \<theta>' s (t' - 1) = signal_of2 False \<theta>' s t"
        using signal_of2_less_ind[OF _ `t < t' - 1`] by metis
      moreover have "\<And>s. signal_of2 False \<theta>' s t = \<sigma> s"
        using lookup_some_signal_of2 unfolding \<theta>'_def add_to_beh_def using `t < next_time t \<tau>'`
        by (metis (mono_tags, hide_lams) lookup_update)
      finally have "\<And>s. signal_of2 False \<theta>' s (t' - 1) = \<sigma> s"
        by auto }
    ultimately show "\<And>s. signal_of2 False \<theta>' s (t' - 1) = \<sigma> s"
      by auto
  qed
  hence "\<gamma>' = {s. \<sigma>' s \<noteq> signal_of2 False \<theta>' s (t' - 1)}"
    unfolding \<gamma>'_def next_event_alt_def \<sigma>'_def by auto
  thus ?thesis
    using 3 4 5 unfolding \<gamma>'_def t'_def \<theta>'_def \<sigma>'_def context_invariant_def by auto
qed

lemma nonneg_delay_lookup_same:
  assumes "nonneg_delay ss"
  assumes "t, \<sigma>, \<gamma>, \<theta> \<turnstile> <ss, \<tau>> \<longrightarrow>\<^sub>s \<tau>'"
  shows "lookup \<tau> t = lookup \<tau>' t"
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
  hence \<tau>'_def: "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) \<tau> (t + dly)" and "0 < dly"
    by auto
  hence "t < t + dly"
    by auto
  then show ?case
    unfolding \<tau>'_def by (transfer', auto simp add: trans_post_raw_def)
next
  case (Bassign_inert sig exp dly)
  hence \<tau>'_def: "\<tau>' = inr_post sig (beval t \<sigma> \<gamma> \<theta> exp) (\<sigma> sig) \<tau> t dly" and "0 < dly"
    by auto
  have "is_stable dly \<tau> t sig (\<sigma> sig) \<or> \<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    by auto
  moreover
  { assume "is_stable dly \<tau> t sig (\<sigma> sig)"
    hence \<tau>'_def': "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) \<tau> (t + dly)"
      unfolding \<tau>'_def inr_post_def by auto
    have "t < t + dly"
      using `0 < dly` by auto
    hence ?case
      unfolding \<tau>'_def' by (transfer', auto simp add: trans_post_raw_def) }
  moreover
  { assume "\<not> is_stable dly \<tau> t sig (\<sigma> sig)"
    hence \<tau>'_def': "\<tau>' = trans_post sig (beval t \<sigma> \<gamma> \<theta> exp) (purge dly \<tau> t sig (\<sigma> sig)) (t + dly)"
      unfolding \<tau>'_def inr_post_def by auto
    have "t < t + dly"
      using `0 < dly` by auto
    hence "lookup \<tau>' t = lookup (purge dly \<tau> t sig (\<sigma> sig)) t"
      unfolding \<tau>'_def' by (transfer', auto simp add: trans_post_raw_def)
    also have "... = lookup \<tau> t"
      using purge_before_now_unchanged by (metis order_refl)
    finally have "lookup \<tau> t = lookup \<tau>' t"
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
  have "\<And>n. n < t \<Longrightarrow> lookup \<tau> n = 0"
    using assms(1) unfolding context_invariant_def by auto
  hence 0: "\<And>n. n < t \<Longrightarrow> lookup \<tau>' n = 0"
    using assms(2) b_seq_exec_preserve_trans_removal by blast
  have "\<And>s. s \<in> dom (lookup \<tau> t) \<Longrightarrow> \<sigma> s = the (lookup \<tau> t s)"
    using assms(1) unfolding context_invariant_def by auto
  hence "\<And>s. s \<in> dom (lookup \<tau>' t) \<Longrightarrow> \<sigma> s = the (lookup \<tau>' t s)"
    using nonneg_delay_lookup_same[OF assms(3) assms(2)] by auto
  with 0 show ?thesis
    using assms(1) unfolding context_invariant_def by auto
qed

lemma poly_mapping_degree:
  "(LEAST n. \<forall>t \<ge> n. lookup \<tau> t = 0) = Poly_Mapping.degree \<tau>"
proof (rule Least_equality)
  show " \<forall>t\<ge>Poly_Mapping.degree \<tau>. lookup \<tau> t = 0"
    by (simp add: beyond_degree_lookup_zero)
next
  fix y
  { assume "y < Poly_Mapping.degree \<tau>"
    hence "Poly_Mapping.degree \<tau> - 1 \<ge> y" and "0 < Poly_Mapping.degree \<tau>" 
      by auto
    moreover have "lookup \<tau> (Poly_Mapping.degree \<tau> - 1) \<noteq> 0"
      using degree_greater_zero_in_keys[OF `0 < Poly_Mapping.degree \<tau>`] by auto
    ultimately have "\<exists>t \<ge> y. lookup \<tau> t \<noteq> 0"
      by auto }
  thus "\<forall>t\<ge>y. lookup \<tau> t = 0 \<Longrightarrow> Poly_Mapping.degree \<tau> \<le> y "
    using leI by blast
qed  

lemma degree_alt_def:
  "Poly_Mapping.degree \<tau> = (LEAST n. \<forall>t \<ge> n. lookup \<tau> t = 0)"
  using poly_mapping_degree[THEN sym] by auto 

lemma
  assumes "context_invariant t \<sigma> \<gamma> \<theta> \<tau>"
  shows "Poly_Mapping.degree \<theta> \<le> t"
proof -
  have "\<forall>k \<ge> t. lookup \<theta> k = 0"
    using assms unfolding context_invariant_def by auto
  thus ?thesis
    unfolding degree_alt_def by (simp add: Least_le)
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

inductive b_simulate :: "time \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal trace \<Rightarrow> bool" where
  "     init' 0 def_state {} 0 cs empty_trans = \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def_state = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def_state = \<gamma>'
   \<Longrightarrow>  add_to_beh def_state 0 0 t' = beh'
   \<Longrightarrow>  maxtime, t', \<sigma>', \<gamma>', beh' \<turnstile> <cs, \<tau>'> \<leadsto> res
   \<Longrightarrow>  b_simulate maxtime cs res"

inductive b_simulate2 :: "time \<Rightarrow> 'signal conc_stmt \<Rightarrow> 'signal transaction \<Rightarrow> 'signal trace \<Rightarrow> bool"
  where
  "     init' 0 def_state {} 0 cs \<tau> = \<tau>'
   \<Longrightarrow>  next_time  0 \<tau>' = t'
   \<Longrightarrow>  next_state 0 \<tau>' def_state = \<sigma>'
   \<Longrightarrow>  next_event 0 \<tau>' def_state = \<gamma>'
   \<Longrightarrow>  add_to_beh def_state 0 0 t' = beh'
   \<Longrightarrow>  maxtime, t', \<sigma>', \<gamma>', beh' \<turnstile> <cs, \<tau>'> \<leadsto> res
   \<Longrightarrow>  b_simulate2 maxtime cs \<tau> res"

text \<open>Judgement @{term "b_simulate"} contains one rule only: executing the @{term "init'"} rule
before @{term "b_simulate_fin"}.\<close>

inductive_cases bau_init : "b_simulate maxtime cs res"
inductive_cases bsim2 : "b_simulate2 maxtime cs \<tau> res"

lemma case_bau':
  assumes "b_simulate maxtime cs res"
  assumes "init' 0 def_state {} 0 cs empty_trans = \<tau>'"
  shows "maxtime, next_time  0 \<tau>', next_state 0 \<tau>' def_state, next_event 0 \<tau>' def_state,
                             add_to_beh def_state 0 0 (next_time  0 \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> res"
  using bau_init[OF assms(1)] assms by auto

lemma bsimulate2_obt_big_step:
  assumes "b_simulate2 maxtime cs \<tau> res"
  assumes "init' 0 def_state {} 0 cs \<tau> = \<tau>'"
  shows "maxtime, next_time  0 \<tau>', next_state 0 \<tau>' def_state, next_event 0 \<tau>' def_state,
                             add_to_beh def_state 0 0 (next_time  0 \<tau>') \<turnstile> <cs, \<tau>'> \<leadsto> res"
  using bsim2[OF assms(1)] assms by auto

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
                                        \<theta>' = add_to_beh \<sigma> \<theta> t t'
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
                , add_to_beh \<sigma> \<theta> t t')) =
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
                , add_to_beh \<sigma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
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
           , add_to_beh \<sigma> \<theta> t t')) = (t', \<sigma>', \<gamma>', \<theta>')"
  hence t'_def: "t' = next_time t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>))" and
        \<sigma>'_def: "\<sigma>' = next_state t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>" and
        \<gamma>'_def: "\<gamma>' = next_event t (b_conc_exec t \<sigma> \<gamma> \<theta> cs (rem_curr_trans t \<tau>)) \<sigma>" and
        \<theta>'_def: "\<theta>' = add_to_beh \<sigma> \<theta> t t'"
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